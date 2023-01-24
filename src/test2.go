package main
import "fmt"

func main(){
     fmt.Print("1 + 2 = ",1 + 2," \n15 modulo 5 = ",15 % 5)

     blup()
}

func blup(){
     fmt.Print("\n5 == 2+3 renvoie ", 5==2+3)
     fmt.Print("\n")
     fmt.Print("6 != 5 renvoie ", 6!=5)
     fmt.Print("\n")
}

