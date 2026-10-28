module
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.Cases
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.Certificates

/-!
# Forward evaluation for shared short-element certificates

The executable maps retain the literal left products in the Parrott normal
forms and double-coset words. Their equality with the existing permutations
allows order checks and normal-form arithmetic to share the certified maps.
Source: Parrott (1972), section 5, p.683; the parent `source/README.md`.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates
open ConverseLocalCoverage DoubleCosetCertificate OuterOddSubgroups.OverlapCentralizers

def permAction : Equiv.Perm (Fin 1600) →* Function.End (Fin 1600) where
  toFun p := p.toFun
  map_one' := rfl
  map_mul' _ _ := rfl

def pointGenerator (j : Fin 10) : Function.End (Fin 1600) := Packed.pointMap j

theorem pointGenerator_eq (j : Fin 10) : pointGenerator j = permAction (Packed.perm j) := rfl

def normalMap (n : Fin 2048) : Function.End (Fin 1600) :=
  pointGenerator 2 ^ (n.val % 2) *
  pointGenerator 3 ^ (n.val / 2 % 2) *
  pointGenerator 4 ^ (n.val / 4 % 4) *
  pointGenerator 5 ^ (n.val / 16 % 2) *
  pointGenerator 6 ^ (n.val / 32 % 4) *
  pointGenerator 7 ^ (n.val / 128 % 2) *
  pointGenerator 8 ^ (n.val / 256 % 4) *
  pointGenerator 9 ^ (n.val / 1024 % 2)

theorem normalMap_eq (n : Fin 2048) : normalMap n = permAction (fastNormalForm n) := by
  simp only [normalMap, pointGenerator_eq, fastNormalForm, map_mul, map_pow]

def repMap (k : Fin 18) : Function.End (Fin 1600) :=
  ((doubleCosetWord k).map fun a => pointGenerator (code a)).prod

theorem repMap_eq (k : Fin 18) : repMap k = permAction (fastRep k) := by
  rw [fastRep, map_list_prod]
  simp only [repMap, List.map_map, pointGenerator_eq]
  rfl

def orderTest (n : Fin 2048) (k : Fin 18) : Bool :=
  let y := normalMap n * repMap k
  (y ^ 13) 0 == 0 && (y ^ 13) 1 == 1 && (y ^ 13) 2 == 2 &&
    (y 0 != 0 || y 1 != 1 || y 2 != 2)

theorem orderTest_eq (n : Fin 2048) (k : Fin 18) : orderTest n k = shortTest n k := by
  simp only [orderTest, normalMap_eq, repMap_eq, ← map_mul, ← map_pow]
  rfl

theorem normalMap_apply (n : Fin 2048) (p : Fin 1600) :
    normalMap n p = (atlas1600SylowTwoNormalForm n).val p := by
  rw [normalMap_eq, normalForm_val]
  rfl

theorem orderTest_sound (n : Fin 2048) (k : Fin 18) (h : orderTest n k = true) :
    orderOf (shortElement n k) = 13 :=
  shortTest_sound n k ((orderTest_eq n k) ▸ h)

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates
