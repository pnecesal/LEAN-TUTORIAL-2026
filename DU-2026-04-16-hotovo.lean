/- ========================== -/
/-  maximum ze čtverce ve 2D  -/
/- ========================== -/

def maximum_z_radku_2D (g : Nat → Nat → Nat) (i : Nat) : Nat → Nat
| 0   => 0
| j+1 => Nat.max (g i j) (maximum_z_radku_2D g i j)

def maximum_z_obdelnika_2D (g : Nat → Nat → Nat) (j : Nat) : Nat → Nat
| 0   => 0
| i+1 => Nat.max (maximum_z_radku_2D g i j) (maximum_z_obdelnika_2D g j i)

def maximum_ze_ctverce (g : Nat → Nat → Nat) (n : Nat) : Nat :=
maximum_z_obdelnika_2D g n n

#eval maximum_z_radku_2D (fun x y => 500-(x-4)^2-(y-5)^2) 10 10

#eval maximum_ze_ctverce (fun x y => 500-(x-4)^2-(y-5)^2) 10

/- ========================= -/
/-  maximum z krychle ve 3D  -/
/- ========================= -/

def maximum_z_radku_3D (g : Nat → Nat → Nat → Nat) (i j : Nat) : Nat → Nat
| 0   => 0
| k+1 => Nat.max (g i j k) (maximum_z_radku_3D g i j k)

def maximum_z_obdelnika_3D (g : Nat → Nat → Nat → Nat) (i k : Nat) : Nat → Nat
| 0   => 0
| j+1 => Nat.max (maximum_z_radku_3D g i j k) (maximum_z_obdelnika_3D g i k j)

def maximum_z_kvadru_3D (g : Nat → Nat → Nat → Nat) (j k : Nat) : Nat → Nat
| 0   => 0
| i+1 => Nat.max (maximum_z_obdelnika_3D g i j k) (maximum_z_kvadru_3D g j k i)

def maximum_z_krychle (g : Nat → Nat → Nat → Nat) (n : Nat) : Nat :=
maximum_z_kvadru_3D g n n n

#eval maximum_z_krychle (fun x y z => x + y - z) 10    /- `18` -/
#eval maximum_z_krychle (fun x y z => x * (6-x) * y * (4-y) * z * (10-z)) 7    /- `900` -/

/- ===================== -/
/-  test prvočíselnosti  -/
/- ===================== -/

def nejvetsi_delitel (a : Nat) : Nat → Nat
| 0   => 0
| n+1 => if a % n = 0 then n else nejvetsi_delitel a n

#eval nejvetsi_delitel 13 13

def je_prvocislo (a : Nat) : Bool :=
nejvetsi_delitel a a == 1

#eval je_prvocislo 23

def vypis_splnujici_do (podminka : Nat → Bool) (n : Nat) :=
List.filter podminka (List.range (n+1))

def seznam_prvocisel_do (n : Nat) :=
vypis_splnujici_do je_prvocislo n

#eval seznam_prvocisel_do 40
#eval seznam_prvocisel_do 100

/- ================ -/
/-  dokonalá čísla  -/
/- ================ -/

def soucet_delitelu (a : Nat) : Nat → Nat
| 0   => 0
| n+1 => if a % n = 0 then (n + soucet_delitelu a n) else soucet_delitelu a n

#eval soucet_delitelu 4 4

def je_dokonale_cislo (a : Nat) : Bool :=
a > 0 ∧ (soucet_delitelu a a == a)

#eval je_dokonale_cislo 0

def seznam_dokonalych_cisel_do (n : Nat) :=
vypis_splnujici_do je_dokonale_cislo n

#eval seznam_dokonalych_cisel_do 500    /- [6, 28, 496] -/
#eval seznam_dokonalych_cisel_do 10000  /- [6, 28, 496, 8128] -/
