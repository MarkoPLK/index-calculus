package main

import (
	"fmt"
	"math/big"
	"os"
	"retos"
	"time"

)

const (
    nRelaciones = 20
    nPrimos = 13
    maxIntentos = 25
)


func main() {
    fmt.Println("Index Calculus para el cálculo del logaritmo discreto...")
    
    var problemas []retos.Reto
    var err error
    if len(os.Args) > 1 {
        fmt.Println("Cargando problemas de talla ", os.Args[1])        
        problemas, err = retos.CargarProblemasTalla(os.Args[1])
    } else {
        // problemas, err = retos.CargarProblemas(retos.Retos1);

        // BUG en la generacion de relaciones ?¿?¿?¿
        // problemas, err = retos.CargarProblema(42, 4026115085191, 2, 1112211128233, 1109122613);
        // problemas, err = retos.CargarProblema(42, 3159178655389, 6, 906853386948, 3159178655388);

        // Problema irresoluble 
        // problemas, err = retos.CargarProblema(32, 2703258601, 87, 1034037786, 1351629300);

        problemas, err = retos.CargarProblema(44, 10876265372701, 2, 9792928529775, 10876265372700);
    }

    if err != nil {
        fmt.Println("Error en la carga de problemas: " + err.Error())
    }

    aciertos := 0
    totalStart := time.Now()
    
    fmt.Println("Generando base de primos...")
    basePrimos := generarBasePrimos(nPrimos)
    debugPrimos(basePrimos)


    for pi, p := range problemas {
        start := time.Now()
        fmt.Printf("[%d] Talla = %d, α = %v, β = %v, m = %v, orden n = %v\n",
            pi, p.Talla, p.Alpha, p.Beta, p.Mod, p.Orden)

        logDisc, err := indexCalculus(&p, basePrimos)
        if err != nil {
            fmt.Println("no se puede resolver: ", err)
            totalStart = totalStart.Add(time.Now().Sub(start))
            continue
        }

        fmt.Printf("[%v] Resultado del logaritmo discreto = %v\n", time.Now().Sub(start), logDisc)

        if retos.ComprobacionLD(p.Alpha, logDisc, p.Mod, p.Beta) {
            aciertos++
        }
        fmt.Println("--------------------------------------------------------")
    }

    fmt.Printf("[%v] Aciertos: %.2f%%, %d/%d\n",
    time.Now().Sub(totalStart), 
    float64(aciertos)/float64(len(problemas))*100,
    aciertos, len(problemas))
}

func generarBasePrimos(size int) []*big.Int {
    primos := []*big.Int{}

    i := big.NewInt(2)
    for len(primos) < size {
        if i.ProbablyPrime(20) {
            primos = append(primos, new(big.Int).Set(i))
        }
        i.Add(i, big.NewInt(1))
    }
    return primos
}

// Devuelve si n es S-Smooth y los factores en dicho caso
func esSmooth(n *big.Int, primos []*big.Int) (bool, map[*big.Int]int) {
    factores := make(map[*big.Int]int)
    restante := new(big.Int).Set(n)

    for _, p := range primos {
        cont := 0
        for new(big.Int).Mod(restante, p).Cmp(big.NewInt(0)) == 0 {
            restante.Div(restante, p)
            cont++
        }
        if cont > 0 {
            factores[p] = cont
        }
    }

    if restante.Cmp(big.NewInt(1)) == 0 {
        return true, factores
    }

    return false, nil
}


func matrizAumentada(expR, primos []*big.Int, relaciones [][]int) [][]*big.Int {
    rows := len(relaciones) // filas
    cols := len(primos)    // columnas
    // Matriz aumnetada [ A | b ] -> A log_alpha p = b 
    matrizAum := make([][]*big.Int, rows)
    for i := 0; i < rows; i++ {
        tempR := make([]*big.Int, cols)
        for j := 0; j < cols; j++ {
            tempR[j] = big.NewInt(int64(relaciones[i][j]))
        }
        matrizAum[i] = append(tempR, new(big.Int).Set(expR[i]))
    }
    return matrizAum
}

func resolverSistema(
    primos []*big.Int,
    matrizAum [][]*big.Int,
    n *big.Int) bool {
        rows := len(matrizAum) // filas
        cols := len(primos)    // columnas

        // Eliminación Gaussiana
        for c := 0; c < cols; c++ {
            // Encontrar un pivote no nulo en la columna
            pivoteFila := -1
            for f := c; f < rows; f++ {
                if matrizAum[f][c].Cmp(big.NewInt(0)) != 0 {
                    pivoteFila = f
                    break
                }
            }

            // Si no hay pivote continuar con otra columna
            if pivoteFila == -1 {
                debugSistema(matrizAum, primos, fmt.Sprintf("No hay pivote en la columna %d\n", c))
                return false
            }

            // Intercambiar filas si es necesario
            if pivoteFila != c {
                matrizAum[c], matrizAum[pivoteFila] =  matrizAum[pivoteFila], matrizAum[c]
            }

            if !findAndSwapPivot(matrizAum, c, n) {
                debugSistema(
                    matrizAum,
                    primos,
                    fmt.Sprintf("No se encontró un pivote válido en la columna %d\n", c))
                return false
            }

            // Escalar el pivote a 1 módulo n
            pivote := new(big.Int).ModInverse(matrizAum[c][c], n)
            if pivote == nil {
                fmt.Printf("Error: el pivote %v no tiene inverso modular\n", matrizAum[c][c])
                return false
            }

            // Escalar el resto de columnas de la fila multiplicacion mod
            for j := c; j <= cols; j++ {
                matrizAum[c][j].Mul(matrizAum[c][j], pivote).Mod(matrizAum[c][j], n)
            }

            // Reducir otras filas
            for f := 0; f < rows; f++ {
                if f == c {
                    continue
                }

                factor := new(big.Int).Set(matrizAum[f][c])
                for j := 0; j <= cols; j++ {
                    temp := new(big.Int).Mul(matrizAum[c][j], factor)
                    matrizAum[f][j].Sub(matrizAum[f][j], temp).Mod(matrizAum[f][j], n)
                }
            }
        }

        return true
}

// Resolver sistema triangular superior
func resolverSistemaTriangSup(
    matriz [][]*big.Int, primos []*big.Int, n *big.Int) map[*big.Int]*big.Int {
        cols := len(primos)
        debugSistema(matriz, primos, "Resolver sistema triangular superior")
        x := make([]*big.Int, cols)
        for i := 0; i < cols; i++ {
            x[i] = big.NewInt(0)
        }

        for i := cols - 1; i >= 0; i-- {
            x[i].Set(matriz[i][cols])
            for j := i + 1; j < cols; j++ {
                temp := new(big.Int).Mul(matriz[i][j], x[j])
                x[i].Sub(x[i], temp).Mod(x[i], n)
            }
        }

        logaritmos := make(map[*big.Int]*big.Int, cols)
        for i, l := range x {
            logaritmos[primos[i]] = l
        }
        return logaritmos
}

func indexCalculus(
    prob *retos.Reto,
    basePrimos []*big.Int) (*big.Int, error) {
        alpha := prob.Alpha
        beta := prob.Beta
        n := prob.Mod
        m := prob.Orden
        r := big.NewInt(1)

        fmt.Printf("Generando %d relaciones lineales ...\n", nRelaciones)
        expR, relaciones := generarRelacionesLineales(alpha, n, r, basePrimos, nRelaciones)

        matrizAum := matrizAumentada(expR, basePrimos, relaciones)

        // fmt.Println("Resolver sistema de ecuaciones...")
        // debugSistema(
        //     matrizAum,
        //     basePrimos,"Resolver sistema de ecuaciones...")

        intentos := 0
        for intentos < maxIntentos &&  !resolverSistema(basePrimos, matrizAum, m) {
            matrizAum = generarRelacionesAdicionales(alpha, n, r, basePrimos, 10, matrizAum)
            intentos++
        }

        if intentos == maxIntentos {
            return nil, fmt.Errorf("no se pudieron generar relaciones adicionales válidas")
        }

        logs := resolverSistemaTriangSup(matrizAum, basePrimos, m)
        debugLogaritmos(logs)

        for {
            alphaR := new(big.Int).Exp(alpha, r, n)
            betaXalphaR := alphaR.Mul(alphaR, beta).Mod(alphaR, n)

            if smooth, factores := esSmooth(betaXalphaR, basePrimos); smooth {
                result := big.NewInt(0)
                fmt.Printf("βα^%v = ", r)
                debugFactores(factores, n)
                for f, c := range factores {
                    if c > 0 {
                        temp := new(big.Int).Mul(big.NewInt(int64(c)), logs[f])
                        result.Add(result, temp)
                    }
                }
                result.Sub(result, r).Mod(result, m)
                return result, nil
            }
            r.Add(big.NewInt(1),r)
        }
}

func findAndSwapPivot(matriz [][]*big.Int, col int, m *big.Int) bool {
    for row := col; row < len(matriz); row++ {
        // Verificar si el elemento en augmented[row][col] es coprimo con m
        gcd := new(big.Int).GCD(nil, nil, matriz[row][col], m)
        if gcd.Cmp(big.NewInt(1)) == 0 {
            // Intercambiar filas
            matriz[col], matriz[row] = matriz[row], matriz[col]
            return true
        }
    }

    return false // No se encontró un pivote válido
}



func generarRelacionesLineales(
    alpha, n, r *big.Int,
    primos []*big.Int,
    cant int) ([]*big.Int, [][]int) {
        relaciones := [][]int{}
        exponentesR := []*big.Int{}

        // Comprobacion de que aparecen todos los factores
        suficiente := make(map[*big.Int]bool) 

        // progress := pb.StartNew(cant)

        for (len(relaciones) < cant) || (len(suficiente) != len(primos)) {
            alphaR := new(big.Int).Exp(alpha, r, n) // alpha^r mod n

            if smooth, factores := esSmooth(alphaR, primos); smooth {
                exponentesR = append(exponentesR, new(big.Int).Set(r))
                    
                // Generar relacion lineal 
                relacion := make([]int, len(primos))
                for i, p := range primos {
                    if cont, exists := factores[p]; exists {
                        suficiente[p] = true
                        relacion[i] = cont
                    }
                }
                relaciones = append(relaciones, relacion)
                // debugRelacionR(len(relaciones), r, primos, relacion, n)
                debugRelacionAlphaR(len(relaciones), r, primos, relacion, n)
            }
            r.Add(r, big.NewInt(1))
        }
        return exponentesR, relaciones
}

func generarRelacionesAdicionales(
    alpha, n, r *big.Int,    // Generador y módulo del grupo
    primos []*big.Int,      // Base de primos
    numRelaciones int,      // Número de relaciones adicionales a generar
    matriz [][]*big.Int,  // Matriz aumentada actual
) [][]*big.Int {
    i := 0
    for i < numRelaciones {
        alphaR := new(big.Int).Exp(alpha, r, n) // alpha^r mod n

        if smooth, factores := esSmooth(alphaR, primos); smooth {
            // Generar relacion lineal 
            relacion := make([]*big.Int, len(primos)+1)
            fmt.Printf("Nueva relación añadida: α^%d ≡ ", r)
            for i, p := range primos {
                if cont, exists := factores[p]; exists {
                    fmt.Printf("%d^%d · ", primos[i], cont)
                    relacion[i] = big.NewInt(int64(cont))
                } else {
                    relacion[i] = big.NewInt(0)
                }
            }
            fmt.Println("mod", n)
            relacion[len(relacion)-1] = new(big.Int).Set(r)
            matriz = append(matriz, relacion)
            i++
        }
        r.Add(r, big.NewInt(1))
    }
    return matriz
}

func factorizacionPrimos(n *big.Int) ([]*big.Int, []*big.Int) {
	factores := []*big.Int{}
	exp := []*big.Int{}
	restante := new(big.Int).Set(n)

	// Manejar el factor 2
	primo := big.NewInt(2)
	if restante.Bit(0) == 0 { // Verifica si es divisible por 2
		contador := 0
		for new(big.Int).Mod(restante, primo).Cmp(big.NewInt(0)) == 0 {
			restante.Div(restante, primo)
			contador++
		}
		factores = append(factores, new(big.Int).Set(primo))
		exp = append(exp, big.NewInt(int64(contador)))
	}

	// Probar solo números impares a partir de 3
	primo.SetInt64(3)
	limite := new(big.Int).Sqrt(restante).Add(new(big.Int).Sqrt(restante), big.NewInt(1))

	for primo.Cmp(limite) <= 0 {
		if primo.ProbablyPrime(20) { 
			contador := 0
			for new(big.Int).Mod(restante, primo).Cmp(big.NewInt(0)) == 0 {
				restante.Div(restante, primo)
				contador++
			}
			if contador > 0 {
				factores = append(factores, new(big.Int).Set(primo))
				exp = append(exp, big.NewInt(int64(contador)))
			}
		}
		primo.Add(primo, big.NewInt(2)) // Incrementar solo a números impares
		limite.Sqrt(restante).Add(limite.Sqrt(restante), big.NewInt(1)) // Actualizar límite dinámicamente
	}

	// Si queda un factor primo mayor
	if restante.Cmp(big.NewInt(1)) > 0 {
		factores = append(factores, new(big.Int).Set(restante))
        fmt.Printf("fumada %v\n", restante)
		exp = append(exp, big.NewInt(1))
	}

	return factores, exp
}

func debugFactoresPrimos(n *big.Int, msg string) {
        primosBeta, expBeta := factorizacionPrimos(n)
        fmt.Printf(msg+": %v =", n)
        for i := range primosBeta {
            fmt.Printf("%v^%v ", primosBeta[i], expBeta[i])
        }
        fmt.Printf("\n")

}


func debugPrimos(basePrimos []*big.Int) {
    basePrimosString := "S = {"

    for _, p := range basePrimos {
       basePrimosString = basePrimosString + fmt.Sprintf("%v, ", p)
    }
    basePrimosString = basePrimosString[:len(basePrimosString) -2] + "}"
    fmt.Println(basePrimosString)
}

func debugRelacionesAlphaR(expR, basePrimos []*big.Int, relaciones [][]int, mod *big.Int) {
    var debug string
    for i, r := range expR {
        debug = fmt.Sprintf("\tα^%4v = ", r)

        for j, e := range relaciones[i] {
            if e > 0 {
                debug += fmt.Sprintf("%v^%d · ", basePrimos[j], e)  
            }
        }
        debug = debug[:len(debug)-3] + fmt.Sprintf("    (mod %v)", mod)
        fmt.Println(debug)
    }
}
func debugRelacionAlphaR(i int, r *big.Int, basePrimos []*big.Int, relacion []int, mod *big.Int) {
    var debug string
    debug = fmt.Sprintf("   [%d] α^%4v = ",i, r)

    for j, e := range relacion {
        if e > 0 {
            // debug += fmt.Sprintf("%v^%d · ", basePrimos[j], e)  
            debug += fmt.Sprintf("%v^%d * ", basePrimos[j], e)  
        }
    }
    debug = debug[:len(debug)-3] + fmt.Sprintf("    (mod %v)", mod)
    fmt.Println(debug)
}

func debugRelacionR(i int, r *big.Int, basePrimos []*big.Int, relacion []int, mod *big.Int) {
    var debug string
    debug = fmt.Sprintf("  [%d] %4v = ",i, r)

    for j, e := range relacion {
        if e > 0 {
            debug += fmt.Sprintf("%v log_α %d + ", e, basePrimos[j])  
        }
    }
    debug = debug[:len(debug)-3] + fmt.Sprintf("    (mod %v)", mod)
    fmt.Println(debug)
}

func debugRelacionesR(expR, basePrimos []*big.Int, relaciones [][]int, mod *big.Int) {
    var debug string
    for i, r := range expR {
        debug = fmt.Sprintf("\t%4v = ", r)

        for j, e := range relaciones[i] {
            if e > 0 {
                debug += fmt.Sprintf("%v log_α %d + ", e, basePrimos[j])  
            }
        }
        debug = debug[:len(debug)-3] + fmt.Sprintf("    (mod %v)", mod)
        fmt.Println(debug)
    }
}

func debugLogaritmo(primo, log *big.Int) {
    fmt.Printf("\tlog_α %v = %v\n", primo, log)
}

func debugLogaritmos(logs map[*big.Int]*big.Int) {
    for primo, log := range logs {
        fmt.Printf("\tlog_α %v = %v\n", primo, log)
    }
}


func debugFactores(factores map[*big.Int]int, mod *big.Int) {
    var debug string = ""
    for f, c := range factores {
        debug += fmt.Sprintf("%v^%d · ", f, c)
    }
    debug = debug[:len(debug)-3] + fmt.Sprintf("    mod %v\n", mod)
    fmt.Println(debug)
}

func debugSistema(matriz [][]*big.Int, primos []*big.Int, msg string) {
    fmt.Println("--------------------------------------------------------")
    fmt.Println(msg)
    for i := range primos {
        fmt.Printf("log_a(%v)\t", primos[i])
    }
    fmt.Printf("| b\n")

    for _, rel := range matriz {
        for i := range rel {
            if rel[i].Cmp(big.NewInt(0)) == 0 {
                fmt.Printf("       -\t")
            } else {
                fmt.Printf("%8v\t", rel[i])
            }
        }
        fmt.Printf("\n")
    }
    fmt.Println("--------------------------------------------------------")
}
