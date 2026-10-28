module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.Quotients
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.Parity
public import Mathlib.GroupTheory.Perm.Fin

/-!
# The literal quintet permutation quotient

The pair stabilizer fixes the unique sextet tetrad containing the pair.
Numbering the six source tetrads therefore restricts its actual part action
to a homomorphism on the remaining five. Its kernel equals the kernel of the
ambient six-part action. The earlier H.14 kernel identification and quotient
isomorphism imply that this homomorphism is onto, by the first isomorphism
theorem and finite cardinality. These group-theoretic inputs remain explicit;
no M22 module identification is an input.

Source: Aschbacher--Smith, H.14 and H.15.4, printed pp.396--400.
The source-compatible first tetrad is `{0,2,9,14}`.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
namespace MathieuCode.M22Quintet.CocodeTransfer.NaturalQuotient
noncomputable section

def partNumbering : Fin 6 ≃ SextetPart m22SourceSextet :=
  Equiv.ofBijective (fun i => ⟨m22SourceTetrad i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j h => (by decide : Function.Injective m22SourceTetrad) (congrArg Subtype.val h),
      fun B => by
        obtain ⟨i,_,hi⟩ := Finset.mem_image.mp B.property
        exact ⟨i, Subtype.ext hi⟩⟩

lemma partNumbering_apply (i : Fin 6) : (partNumbering i).val = m22SourceTetrad i := rfl

def partAction : Q →* Equiv.Perm (SextetPart m22SourceSextet) :=
  (sextetPartPerm m22SourceSextet).comp QToSextet

lemma partAction_fixes_first (g : Q) : partAction g (partNumbering 0) = partNumbering 0 := by
  apply sextetPart_eq_of_mem m22SourceSextet _ _ (i := 0)
  · have hp : g.val.val • m22Pair = m22Pair := g.val.property
    have hle := Finset.smul_finset_subset_smul_finset (a := g.val.val) m22Pair_le_sourceTetrad
    rw [hp] at hle
    exact hle (by decide : (0 : Fin 24) ∈ m22Pair)
  · exact (by decide : (0 : Fin 24) ∈ m22SourceTetrad 0)

def sixAction : Q →* Equiv.Perm (Fin 6) :=
  partNumbering.symm.permCongrHom.toMonoidHom.comp partAction

lemma sixAction_fixes_zero (g : Q) : sixAction g 0 = 0 := by
  apply partNumbering.injective
  change partNumbering (partNumbering.symm (partAction g (partNumbering 0))) = _
  rw [partNumbering.apply_symm_apply, partAction_fixes_first]

def remainingAction : Q →* Equiv.Perm {i : Fin 6 // i ≠ 0} where
  toFun g := (sixAction g).subtypePerm (p := fun i => i ≠ 0) (by
    intro i
    conv_lhs => rw [← sixAction_fixes_zero g]
    exact (sixAction g).injective.ne_iff)
  map_one' := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    exact Equiv.congr_fun (map_one sixAction) i.val
  map_mul' g h := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    exact Equiv.congr_fun (map_mul sixAction g h) i.val

def q : Q →* Equiv.Perm (Fin 5) :=
  (finSuccAboveEquiv (0 : Fin 6)).symm.permCongrHom.toMonoidHom.comp remainingAction

lemma q_compatible (g : Q) (i : Fin 5) : (q g i).succ = sixAction g i.succ := by
  have h := (finSuccAboveEquiv (0 : Fin 6)).apply_symm_apply
    ((sixAction g).subtypePerm (p := fun i => i ≠ 0) (by
      intro i
      conv_lhs => rw [← sixAction_fixes_zero g]
      exact (sixAction g).injective.ne_iff)
      (finSuccAboveEquiv (0 : Fin 6) i))
  exact congrArg Subtype.val h

lemma q_part_compatible (g : Q) (i : Fin 5) :
    partNumbering (q g i).succ = partAction g (partNumbering i.succ) := by
  rw [q_compatible]
  exact partNumbering.apply_symm_apply _

lemma q_ker_eq_partAction_ker : q.ker = partAction.ker := by
  ext g
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hg
    apply Equiv.ext
    intro B
    obtain ⟨i,rfl⟩ := partNumbering.surjective B
    refine Fin.cases (partAction_fixes_first g) (fun i => ?_) i
    have hi := q_part_compatible g i
    rw [hg] at hi
    exact hi.symm
  · intro hg
    apply Equiv.ext
    intro i
    apply Fin.succ_injective
    apply partNumbering.injective
    rw [q_part_compatible, hg]
    rfl

lemma relativeCore_eq : K.subgroupOf Q = pCore 2 Q := by
  exact Subgroup.comap_map_eq_self (Subgroup.ker_subtype Q ▸ bot_le)

lemma q_ker (hpart : partAction.ker = pCore 2 Q) : q.ker = K.subgroupOf Q := by
  rw [q_ker_eq_partAction_ker, hpart, relativeCore_eq]

lemma q_surjective (hpart : partAction.ker = pCore 2 Q)
    (e : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 5)) : Function.Surjective q := by
  let f : (Q ⧸ pCore 2 Q) →* Equiv.Perm (Fin 5) :=
    QuotientGroup.lift (pCore 2 Q) q (by rw [q_ker_eq_partAction_ker, hpart])
  have hi : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H g =>
      apply (QuotientGroup.eq_one_iff g).mpr
      have hg : g ∈ q.ker := hx
      rwa [q_ker_eq_partAction_ker, hpart] at hg
  let : Fintype (Q ⧸ pCore 2 Q) := Fintype.ofFinite _
  have hs : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hi, Fintype.card_congr e.toEquiv⟩).surjective
  intro s
  obtain ⟨x,hx⟩ := hs s
  induction x using QuotientGroup.induction_on with
  | H g => exact ⟨g,hx⟩
end
end MathieuCode.M22Quintet.CocodeTransfer.NaturalQuotient
