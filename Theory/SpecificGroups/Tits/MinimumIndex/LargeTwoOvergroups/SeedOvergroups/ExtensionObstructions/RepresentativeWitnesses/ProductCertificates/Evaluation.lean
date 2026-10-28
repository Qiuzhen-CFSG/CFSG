module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.Certificates
/-!
# Checked evaluation for the product witnesses

Natural-number forward evaluation removes permutation structure from the
finite kernel reductions. The comparison lemmas prove it computes exactly
the existing recovery and order tests on the literal Atlas permutations.
Source: Parrott (1972), section 5, p.683; ../source/README.md.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ProductCertificates
open ConverseLocalCoverage.DoubleCosetCertificate OuterOddSubgroups.OverlapCentralizers ConverseLocalCoverage

def point (j : Fin 10) (p : Nat) : Nat :=
 ((![Packed.r1Data, Packed.r8Data, Packed.s1Data, Packed.s2Data, Packed.s3Data,
 Packed.s4Data, Packed.s5Data, Packed.s6Data, Packed.s7Data, Packed.s8Data] j >>> (11*p)) % 2048) % 1600

def normalPoint (n : Fin 2048) (p : Nat) : Nat :=
 (point 2)^[n.val%2] ((point 3)^[n.val/2%2] ((point 4)^[n.val/4%4] ((point 5)^[n.val/16%2]
 ((point 6)^[n.val/32%4] ((point 7)^[n.val/128%2] ((point 8)^[n.val/256%4] ((point 9)^[n.val/1024%2] p)))))))

def repPoint (k : Fin 18) (p : Nat) : Nat :=
 (doubleCosetWord k).foldr (fun a q => point (code a) q) p

def productPoint (ns : List (Fin 2048)) (k : Fin 18) (p : Nat) : Nat :=
 ns.foldr (fun n q => normalPoint n (repPoint k q)) p

def orderTest (ns : List (Fin 2048)) (k : Fin 18) : Bool :=
 let y := productPoint ns k
 y^[13] 0 == 0 && y^[13] 1 == 1 && y^[13] 2 == 2 &&
 (y 0 != 0 || y 1 != 1 || y 2 != 2)

def recoverTest (w : List (Fin 2048)) (u v n : Fin 2048) : Bool :=
 let x := fun p => w.foldr normalPoint (normalPoint u p)
 let y := fun p => normalPoint v (normalPoint n p)
 x 0 == y 0 && x 1 == y 1 && x 2 == y 2

private theorem pow_val (g : Equiv.Perm (Fin 1600)) (f : Nat → Nat)
    (h : ∀ p : Fin 1600, (g p).val = f p.val) (n : Nat) (p : Fin 1600) :
    ((g ^ n) p).val = f^[n] p.val := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => rw [pow_succ, Equiv.Perm.mul_apply, ih, h, Function.iterate_succ_apply]

private theorem point_pow_val (j : Fin 10) (n : Nat) (p : Fin 1600) :
    ((Packed.perm j ^ n) p).val = (point j)^[n] p.val :=
  pow_val _ _ (fun _ => rfl) _ _

theorem normalPoint_val (n : Fin 2048) (p : Fin 1600) :
    (fastNormalForm n p).val = normalPoint n p.val := by
  simp only [fastNormalForm, normalPoint, Equiv.Perm.mul_apply, point_pow_val]

private theorem wordPoint_val (w : List ParrottGenerator) (p : Fin 1600) :
    (((w.map fun a => Packed.perm (code a)).prod) p).val =
      w.foldr (fun a q => point (code a) q) p.val := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, List.foldr_cons]
    change point (code a) _ = _
    rw [ih]

theorem repPoint_val (k : Fin 18) (p : Fin 1600) :
    (fastRep k p).val = repPoint k p.val := wordPoint_val _ _

theorem productPoint_val (ns : List (Fin 2048)) (k : Fin 18) (p : Fin 1600) :
    (((ns.map fun n => fastNormalForm n * fastRep k).prod) p).val =
      productPoint ns k p.val := by
  induction ns generalizing p with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply,
      normalPoint_val, repPoint_val, ih, productPoint, List.foldr_cons]

private theorem normalWord_val (w : List (Fin 2048)) (p : Fin 1600) :
    (((w.map fastNormalForm).prod) p).val = w.foldr normalPoint p.val := by
  induction w generalizing p with
  | nil => rfl
  | cons n w ih =>
    simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply,
      normalPoint_val, ih, List.foldr_cons]

theorem productTest_of_orderTest (ns : List (Fin 2048)) (k : Fin 18)
    (h : orderTest ns k = true) : productTest ns k = true := by
  have h2 : (2 : Fin 1600).val = 2 := rfl
  simpa only [h2, productTest, orderTest, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, pow_val _ _ (productPoint_val ns k),
    productPoint_val] using h

theorem recoveryTest_of_recoverTest (w : List (Fin 2048)) (u v n : Fin 2048)
    (h : recoverTest w u v n = true) : recoveryTest w u v n = true := by
  have h2 : (2 : Fin 1600).val = 2 := rfl
  simpa only [h2, recoveryTest, recoverTest, Bool.and_eq_true, beq_iff_eq,
    Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Equiv.Perm.mul_apply, normalWord_val, normalPoint_val] using h
end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ProductCertificates
