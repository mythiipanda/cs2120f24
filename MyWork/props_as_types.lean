inductive KevinIsFromCharlottesville :  Type where
| cvilleBirthCert
| cvilleDriversLicense
| cvilleUtilityBill

inductive CarterIsFromCharlottesville :  Type where
| cvilleBirthCert
| cvilleDriversLicense
| cvilleUtilityBill

open KevinIsFromCharlottesville
open CarterIsFromCharlottesville

def proofOfKIFC : KevinIsFromCharlottesville := cvilleDriversLicense
def proofOfCIFC : CarterIsFromCharlottesville := cvilleBirthCert
def proofOfNat : Nat := 1
inductive BothAreFromCharlottesville : Type where
| intro (kp : KevinIsFromCharlottesville) (cp : CarterIsFromCharlottesville)
def both : BothAreFromCharlottesville := BothAreFromCharlottesville.intro proofOfKIFC proofOfCIFC
