module
public import Theory.Representation.PSL3Two.DoubledPointOffenders
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import Stellmacher.MaxElementaryOffender
public import Theory.GroupTheory.PCoreImage

/-!
# Baumann normalization for a doubled-natural point centralizer

Let U be a normal elementary subgroup marked as two natural SL₃(2)
modules, with the literal action quotient having kernel O₂(H). A Sylow-fixed
nonidentity element w of U determines a point parabolic. On its radical,
the doubled fixed-space inequality rules out every nontrivial maximum
elementary image. Hence J(O₂(C_H(w))) centralizes U. The centralizing
case of B.2.10 identifies both its Thompson and Baumann subgroups with
those of O₂(H), and gives relative normality in H.

The Chapter13 fixed-core application uses this for the actual selected
component and its reciprocal fixed-line centralizer. It does not assume
shortness, a Baumann-normalization conclusion or a chosen simple summand.
Source: Aschbacher–Smith B.2.10(1), printed p.77, and 13.4.10(4), p.909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
variable {H : Type*} [Group H] [Finite H]

/-- The literal marked doubled-natural point radical has the same Thompson
and Baumann subgroups as the ambient two-core. -/
theorem doubled_point_baumann
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 H)
    (e : U ≃* Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : ∀ h u, (e (MulAut.conjNormal h u)).toAdd =
      (BinaryLinearThree.W.prod BinaryLinearThree.W) (q h) (e u).toAdd)
    (w : U) (hw : w ≠ 1) (S : Sylow 2 H)
    (hSw : (S : Subgroup H) ≤ centralizer ({w.val} : Set H)) :
    let R := (centralizer ({w.val} : Set H)).pCoreIn 2
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ (pCore 2 H) ∧
      baumann R = baumann (pCore 2 H) ∧ (baumann R).Normal := by
  let ρ := BinaryLinearThree.W.prod BinaryLinearThree.W
  let P := centralizer ({w.val} : Set H)
  let R := P.pCoreIn 2
  have hact (h : H) (u : U) :
      ρ (q h) (e u).toAdd = (e u).toAdd ↔ h * u.val = u.val * h := by
    rw [←he,Multiplicative.toAdd.injective.eq_iff,e.injective.eq_iff,Subtype.ext_iff]
    change h * u.val * h⁻¹ = u.val ↔ _
    exact mul_inv_eq_iff_eq_mul
  have hker : q.ker = centralizer (U : Set H) := by
    ext h
    constructor
    · intro hh u hu
      have hh' : q h = 1 := hh
      have hf : ρ (q h) (e ⟨u,hu⟩).toAdd = (e ⟨u,hu⟩).toAdd := by rw [hh',map_one]; rfl
      exact ((hact h ⟨u,hu⟩).mp hf).symm
    · intro hh
      change q h = 1
      apply BinaryLinearThree.natural_injective
      apply LinearMap.ext
      intro x
      obtain ⟨u,hu⟩ := e.surjective (Multiplicative.ofAdd (x,0))
      have hf := (hact h u).mpr (hh u.val u.property).symm
      rw [hu] at hf
      rw [map_one]
      exact congrArg Prod.fst hf
  let v := (e w).toAdd
  have hv : v ≠ 0 := by
    intro hh
    apply hw
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [map_one]
    exact hh
  let S₀ := S.mapSurjective hq
  have hsfix (a : S₀) : ρ a.val v = v := by
    obtain ⟨s,hs,ha⟩ := (show a.val ∈ (S : Subgroup H).map q from a.property)
    rw [←ha]
    exact (hact s w).mpr (mem_centralizer_singleton_iff.mp (hSw hs))
  obtain ⟨v₀,hv₀,hpoint⟩ := BinaryLinearThree.doubled_sylow_fixed_naturalPoint S₀ v hv hsfix
  have hP : P.map q = BinaryLinearThree.naturalPoint v₀ := by
    rw [←hpoint]
    ext g
    constructor
    · rintro ⟨h,hh,rfl⟩
      have hf := (hact h w).mpr (mem_centralizer_singleton_iff.mp hh)
      exact ⟨(BinaryLinearThree.OrbitStabilizers.mem_natural _ _).mpr (congrArg Prod.fst hf),
        (BinaryLinearThree.OrbitStabilizers.mem_natural _ _).mpr (congrArg Prod.snd hf)⟩
    · rintro ⟨h1,h2⟩
      obtain ⟨h,rfl⟩ := hq g
      refine ⟨h,?_,rfl⟩
      exact mem_centralizer_singleton_iff.mpr ((hact h w).mp
        (Prod.ext ((BinaryLinearThree.OrbitStabilizers.mem_natural _ _).mp h1)
          ((BinaryLinearThree.OrbitStabilizers.mem_natural _ _).mp h2)))
  have hRP : R.map q = (BinaryLinearThree.naturalPoint v₀).pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup q (hk.symm ▸ pCore_isPGroup),hP]
  have hQP : pCore 2 H ≤ P := by
    rw [←hk,hker]
    intro h hh
    exact mem_centralizer_singleton_iff.mpr (hh w.val w.property).symm
  have hQR : pCore 2 H ≤ R :=
    le_pCoreIn_of_normalizes pCore_isPGroup hQP (by rw [normalizer_eq_top];exact le_top)
  have hUQ : U ≤ pCore 2 H := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩
  have hUR : U ≤ R := hUQ.trans hQR
  have hfixed (A : Subgroup H) (u : U) :
      u.val ∈ centralizer (A : Set H) ↔ (e u).toAdd ∈ fixedSpace ρ (A.map q) := by
    constructor
    · intro hc a
      obtain ⟨h,hh,ha⟩ := a.property
      change ρ a.val (e u).toAdd = (e u).toAdd
      rw [←ha]
      exact (hact h u).mpr (hc h hh)
    · intro hf a ha
      exact (hact a u).mp (hf ⟨q a,mem_map_of_mem q ha⟩)
  have hcard (A : Subgroup H) :
      Nat.card (U ⊓ centralizer (A : Set H) : Subgroup H) = Nat.card (fixedSpace ρ (A.map q)) := by
    apply Nat.card_congr
    exact {
      toFun := fun u => ⟨(e ⟨u.val,u.property.1⟩).toAdd,(hfixed A _).mp u.property.2⟩
      invFun := fun v => ⟨(e.symm (Multiplicative.ofAdd v.val)).val,
        (e.symm (Multiplicative.ofAdd v.val)).property,
        (hfixed A _).mpr (by simp)⟩
      left_inv := fun u => by apply Subtype.ext; simp
      right_inv := fun v => by apply Subtype.ext; simp }
  have hUc : Nat.card U = 64 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (BinaryLinearThree.Vector × BinaryLinearThree.Vector) = 64
    simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  have hJ : elementaryAbelianMaxJ R ≤ centralizer (U : Set H) := by
    apply sSup_le
    intro A hA
    rw [←hker]
    apply (Subgroup.map_eq_bot_iff _).mp
    by_contra hn
    have hlo := maxElementary_card_le_fixed_mul_image R U A hUR hA q hker
    rw [hUc,hcard] at hlo
    have hhi := BinaryLinearThree.doubled_point_radical_fixed_card_lt v₀ hv₀
      (A.map q) ((map_mono hA.1).trans_eq hRP) hn
    exact (not_lt_of_ge hlo) hhi
  have hcore : pCore 2 H = R ⊓ centralizer (U : Set H) := by
    rw [←hker,hk,inf_eq_right.mpr hQR]
  have hb := lemma_B_2_10_centralizing U R hUR hQR hcore (by rwa [thompsonJ_zero])
  exact ⟨by simpa only [thompsonJ_zero] using hb.1,hb.2.1,hb.2.2.2⟩
end CFSG.Quasithin.ChapterB
