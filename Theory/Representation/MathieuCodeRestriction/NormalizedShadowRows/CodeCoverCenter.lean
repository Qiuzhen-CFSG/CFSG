module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeCentralizer
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCoreCentralLift
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Theory.GroupTheory.FixedElementaryTransport

/-!
# The covering center above the original M22 hexad

A central covering map induces a central map after removing the two-cores.
When the target two-core quotient is centerless, the new kernel is exactly
the image of the old kernel. An odd kernel embeds in this quotient. Apply
this to the full preimage of a hexad stabilizer: its quotient center is
isomorphic to the original M22 covering center. The latter has order
dividing three by the checked multiplier bound twelve and trivial two-core.

Thus a possible cubic center of the A6 residual is inherited from the
original cover; it cannot be discarded just because the faithful module
actor is M22. The original subgroup and quotient application is
NonFFSourceMathieuShadowRows.M22CodeFullCenter.
Source: Aschbacher--Smith, H.13, I.1.3(4), and the covering comparison in
8.2.2(1), printed pp.395,407,715, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering Sporadic.Mathieu
open scoped Pointwise
namespace MathieuCode.NormalizedShadowRows

private theorem quotient_center_eq_kernel_image
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hk : f.ker ≤ center A)
    (hz : center (B ⧸ pCore 2 B) = ⊥) :
    center (A ⧸ pCore 2 A) = f.ker.map (QuotientGroup.mk' (pCore 2 A)) := by
  have hle : pCore 2 A ≤ (pCore 2 B).comap f := by
    rw [f.comap_pCore_of_central_kernel hf hk]
    exact le_sup_left
  let g := QuotientGroup.map (pCore 2 A) (pCore 2 B) f hle
  have hg : Function.Surjective g := QuotientGroup.map_surjective_of_surjective _ _ _
    ((QuotientGroup.mk'_surjective _).comp hf) _
  have hker : g.ker = f.ker.map (QuotientGroup.mk' (pCore 2 A)) := by
    rw [QuotientGroup.ker_map, f.comap_pCore_of_central_kernel hf hk,
      Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  apply le_antisymm
  · rw [←hker]
    intro x hx
    have hh : g x ∈ center (B ⧸ pCore 2 B) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨y,rfl⟩ := hg y
      rw [←map_mul,←map_mul,mem_center_iff.mp hx y]
    simpa only [hz,mem_bot,MonoidHom.mem_ker] using hh
  · rintro _ ⟨x,hx,rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) y
    rw [←map_mul,←map_mul,mem_center_iff.mp (hk hx) y]

private def kernelCoreCenterEquiv
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hk : f.ker ≤ center A)
    (ho : Odd (Nat.card f.ker)) (hz : center (B ⧸ pCore 2 B) = ⊥) :
    f.ker ≃* center (A ⧸ pCore 2 A) := by
  let q := QuotientGroup.mk' (pCore 2 A)
  have hd : Disjoint f.ker (pCore 2 A) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr ho).pow_right n
  let r := q.comp f.ker.subtype
  have hr : Function.Injective r := by
    apply (injective_iff_map_eq_one r).mpr
    intro x hx
    apply Subtype.ext
    exact mem_bot.mp (hd.le_bot ⟨x.property,(QuotientGroup.eq_one_iff _).mp hx⟩)
  have he : r.range = center (A ⧸ pCore 2 A) := by
    rw [MonoidHom.range_comp,range_subtype]
    exact (quotient_center_eq_kernel_image f hf hk hz).symm
  exact (MonoidHom.ofInjective hr).trans (MulEquiv.subgroupCongr he)

/-- The full hexad preimage retains precisely the original odd covering center. -/
theorem code_hexad_cover_center_equiv {Y : Type*} [Group Y] [Finite Y]
    (c : Cover Y M22) (hcore : pCore 2 Y = ⊥)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    let P := (MulAction.stabilizer M22 B).comap c.toMonoidHom
    Nonempty (center (P ⧸ pCore 2 P) ≃* center Y) := by
  let S := MulAction.stabilizer M22 B
  let P := S.comap c.toMonoidHom
  let f := c.toMonoidHom.subgroupComap S
  have hf : Function.Surjective f :=
    c.toMonoidHom.subgroupComap_surjective_of_surjective S c.surjective
  have hk : f.ker ≤ center P := by
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp
      (c.ker_le_center (show c.toMonoidHom x = 1 from congrArg Subtype.val hx)) y)
  have hc : c.toMonoidHom.ker = center Y := by
    have hh := c.comap_center
    rwa [m22_center_eq_bot,MonoidHom.comap_bot] at hh
  let j : f.ker →* c.toMonoidHom.ker := {
    toFun x := ⟨x.val.val,congrArg Subtype.val x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Bijective j := by
    constructor
    · intro x y he
      exact Subtype.ext (Subtype.ext (congrArg (fun x : c.toMonoidHom.ker => (x : Y)) he))
    · intro x
      have hm : x.val ∈ P := by
        change c.toMonoidHom x.val ∈ S
        rw [show c.toMonoidHom x.val = 1 from x.property]
        exact S.one_mem
      exact ⟨⟨⟨x.val,hm⟩,Subtype.ext x.property⟩,rfl⟩
  let e := MulEquiv.ofBijective j hj
  have ho : Odd (Nat.card f.ker) := by
    rw [Nat.card_congr e.toEquiv]
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    exact not_dvd_card_central_of_pCore_eq_bot hcore _ c.ker_le_center
  have hz : center (S ⧸ pCore 2 S) = ⊥ := by
    have hh := FixedElementary.map_center (code_hexad_core_equiv hB)
    rw [alternatingGroup.center_eq_bot (by simp)] at hh
    exact (map_eq_bot_iff_of_injective _ (code_hexad_core_equiv hB).injective).mp hh
  exact ⟨(kernelCoreCenterEquiv f hf hk ho hz).symm.trans
    (e.trans (MulEquiv.subgroupCongr hc))⟩

/-- The full covering center above M22 is either trivial or cubic once its
intrinsic two-core has been removed. -/
theorem code_cover_center_card_dvd_three {Y : Type*} [Group Y] [Finite Y]
    (c : Cover Y M22) (hcore : pCore 2 Y = ⊥) : Nat.card (center Y) ∣ 3 := by
  have hk : c.toMonoidHom.ker = center Y := by
    have hh := c.comap_center
    rwa [m22_center_eq_bot,MonoidHom.comap_bot] at hh
  have hd := M22UniversalMultiplier.kernel_card_dvd_twelve c
  have hn := not_dvd_card_central_of_pCore_eq_bot hcore _ c.ker_le_center
  rw [hk] at hd hn
  have hb := Nat.le_of_dvd (by decide : 0 < 12) hd
  generalize Nat.card (center Y) = n at *
  interval_cases n <;> norm_num at *

/-- A cubic projective covering center above the hexad produces an actual
cubic in the original action kernel, surviving the original two-core map. -/
theorem code_hexad_cubic_kernel {R : Type*} [Group R] [Finite R]
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (f : R →* MulAction.stabilizer M22 B) (hf : Function.Surjective f)
    (e : ((R ⧸ pCore 2 R) ⧸ center (R ⧸ pCore 2 R)) ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (center (R ⧸ pCore 2 R)) = 3) :
    ∃ x : R, f x = 1 ∧ orderOf x = 3 ∧ QuotientGroup.mk' (pCore 2 R) x ≠ 1 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.card (R ⧸ pCore 2 R) = 1080 := by
    rw [card_eq_card_quotient_mul_card_subgroup (center (R ⧸ pCore 2 R)),hz,
      Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hd : 27 ∣ Nat.card R := (show 27 ∣ Nat.card (R ⧸ pCore 2 R) by
    rw [hc]; decide).trans (card_quotient_dvd_card _)
  have hn := f.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top,m22Hexad_stabilizer_card hB] at hn
  rw [←hn] at hd
  have h27 : 27 ∣ 9 * Nat.card f.ker := by
    apply (show Nat.Coprime 27 640 from by decide).dvd_of_dvd_mul_right
    convert hd using 1; ring
  have h3 : 3 ∣ Nat.card f.ker := by
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 9)).mp h27
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 3 h3
  have ho : orderOf (x : R) = 3 := (orderOf_coe x).trans hx
  refine ⟨x,x.property,ho,?_⟩
  intro hh
  have hm : (x : R) ∈ pCore 2 R := (QuotientGroup.eq_one_iff _).mp hh
  have ho' : orderOf (⟨x,hm⟩ : pCore 2 R) = 3 := (orderOf_coe _).symm.trans ho
  have hd3 := orderOf_dvd_natCard (⟨x,hm⟩ : pCore 2 R)
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := R)).exists_card_eq
  rw [ho',hn] at hd3
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd3)

end MathieuCode.NormalizedShadowRows
