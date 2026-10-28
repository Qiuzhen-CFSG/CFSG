module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus.Marked
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# A Weyl lift normalizing the original cubic torus

The actual order-three subgroup lies in K because L₁≤K for the literal
two-residuals. It is Sylow-three in K: the original quotient has two-group
kernel and embeds every three-subgroup into S₅, whose order has only one
factor of three. The existing Sylow-normalizer image theorem then lifts
the concrete Weyl matrix to N_K(J), preserving its original quotient image.
This is the Sylow-conjugacy correction of an arbitrary quotient lift.

No order-two condition is imposed on the lifted normalizer element. Neither
S≤L₁ nor any conclusion of 14.7.73 is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.63–65 and the involution step of 14.7.72, printed p.1076.
-/

public section
noncomputable section
open Subgroup Representation Matrix.SpecialLinearGroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

private theorem three_sylow {A : Type*} [Group A] [Finite A]
    (f : A →* Equiv.Perm (Fin 5)) (hk : IsPGroup 2 f.ker)
    (P : Subgroup A) (hP : Nat.card P = 3) :
    ∃ S : Sylow 3 A, (S : Subgroup A) = P := by
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨k, hk⟩ := hk.exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  refine ⟨{ P with
    isPGroup' := IsPGroup.of_card (p := 3) (n := 1) (by simpa using hP)
    is_maximal' := ?_ }, rfl⟩
  intro R hR hPR
  have hi := injective_comp_subtype_of_coprime_ker f hcop R hR
  have hcard : Nat.card (R.map f) = Nat.card R := by
    apply Nat.card_image_of_injOn
    intro x hx y hy he
    exact congrArg Subtype.val (hi (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) he)
  have hd : Nat.card R ∣ 120 := by
    rw [← hcard]
    have hh := card_subgroup_dvd_card (R.map f)
    simpa only [Nat.card_perm, Nat.card_fin, show Nat.factorial 5 = 120 from by decide] using hh
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hk1 : k ≤ 1 := by
    by_contra hn
    have h9 : 9 ∣ 120 := (Nat.pow_dvd_pow 3 (show 2 ≤ k by omega)).trans (hk ▸ hd)
    norm_num at h9
  symm
  apply eq_of_le_of_card_ge hPR
  rw [hP, hk]
  exact (Nat.pow_le_pow_right (by decide : 0 < 3) hk1)

omit [Finite G] in
private theorem local_le_K : F.Li L 1 ≤ K F := by
  intro x hx
  change x ∈ (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype at hx
  obtain ⟨n, hn, rfl⟩ := hx
  let f : (L ⊓ F.H : Subgroup G) →* F.H := inclusion inf_le_right
  exact mem_map.mpr ⟨f n, map_pResidual_le 2 f (mem_map.mpr ⟨n, hn, rfl⟩), rfl⟩

/-- Lift the concrete Weyl matrix through the Sylow-three normalizer in K.
The normalizer element retains its exact quotient image; its order is unrestricted. -/
theorem MarkedTorus.exists_mover (t : MarkedTorus d) :
    ∃ n : F.H, (n : G) ∈ K F ∧ (n : G) ∈ normalizer (t.torus : Set G) ∧
      d.qH n = alternatingActor d.naturalQuotient weyl := by
  let A := (K F).subgroupOf F.H
  let f : A →* Equiv.Perm (Fin 5) := d.qH.comp A.subtype
  let g : A := ⟨t.generator, local_le_K t.generator_mem⟩
  let P : Subgroup A := zpowers g
  have hcard : Nat.card P = 3 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe g]
    exact t.generator_order
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (d.qH.ker.comap A.subtype)
    have hh : IsPGroup 2 d.qH.ker := by
      rw [d.qH_ker]
      exact (isPGroup_pCoreIn 2 F.H).comap_subtype
    exact hh.comap_of_injective A.subtype A.subtype_injective
  obtain ⟨P₃, hP₃⟩ := three_sylow f hk P hcard
  obtain ⟨k, hk⟩ := d.alternatingActor_lift weyl
  let w : f.range := ⟨alternatingActor d.naturalQuotient weyl, ⟨k, hk⟩⟩
  have hw : w ∈ normalizer (((P₃ : Subgroup A).map f.rangeRestrict) : Set f.range) := by
    rw [hP₃, MonoidHom.map_zpowers]
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    have he : (MulAut.conj w) (f.rangeRestrict g) = (f.rangeRestrict g)⁻¹ := by
      apply Subtype.ext
      change alternatingActor d.naturalQuotient weyl * d.qH t.generator *
        (alternatingActor d.naturalQuotient weyl)⁻¹ = (d.qH t.generator)⁻¹
      rw [t.image, ← map_inv, ← map_mul, ← map_mul, weyl_diag, map_inv]
    change zpowers ((MulAut.conj w) (f.rangeRestrict g)) = _
    rw [he, zpowers_inv]
  rw [← P₃.normalizer_map_surjective f.rangeRestrict f.rangeRestrict_surjective] at hw
  obtain ⟨n, hn, he⟩ := hw
  refine ⟨n.val, n.property, ?_, congrArg Subtype.val he⟩
  let i : A →* G := F.H.subtype.comp A.subtype
  have hi : P.map i = t.torus := by
    exact MonoidHom.map_zpowers i g
  have hm := (P.le_normalizer_map i) (mem_map_of_mem i
    (show n ∈ normalizer (P : Set A) from hP₃ ▸ hn))
  rw [hi] at hm
  exact hm


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus
