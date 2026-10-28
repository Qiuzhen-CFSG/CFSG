module
public import Theory.GroupAction.ElementaryEightPointResidual
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Literal conjugation images of cubic residuals on an eight-group

Let a two-perfect subgroup B normalize an elementary abelian subgroup C
of order eight and fix exactly an order-two subgroup Z. If B/O₂(B) has
order three, the actual image of B on C is cubic or isomorphic to A₄.
The cubic alternative holds exactly when the original O₂(B) centralizes C.

The image is defined through B intersect N(C) and the literal normalizer
action. Its kernel is B intersect C(C). The point-image bound and the
faithful four-coset recognition give the alternatives; factoring through
the original two-core proves the precise criterion for the cubic branch.

Source application: Aschbacher–Smith, 14.7.6, printed pp.1044–1045 of
refs/quasithin.pdf, at both endpoints of the selected common three-space.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction.ElementaryEightPointResidual
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Literal conjugation on the common three-space, with its original actor. -/
def conjugationAction (B C : Subgroup G) (hn : B ≤ normalizer (C : Set G)) : B →* MulAut C :=
  C.normalizerMonoidHom.comp (inclusion hn)

/-- The image of the literal residual normalizer on C; this definition
retains the ambient intersection even before normalization is supplied. -/
def conjugationImage (B C : Subgroup G) : Subgroup (MulAut C) :=
  (B.subgroupOf (normalizer (C : Set G))).map C.normalizerMonoidHom

omit [Finite G] in
/-- For an actor normalizing C, the image is the range of its literal action. -/
theorem conjugationImage_eq_range (B C : Subgroup G)
    (hn : B ≤ normalizer (C : Set G)) : conjugationImage B C = (conjugationAction B C hn).range := by
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨⟨b,hb⟩,rfl⟩
  · rintro ⟨b,rfl⟩
    exact ⟨⟨b,hn b.property⟩,b.property,rfl⟩

omit [Finite G] in
/-- Evaluation retains the original ambient conjugation convention. -/
theorem conjugationAction_apply (B C : Subgroup G)
    (hn : B ≤ normalizer (C : Set G)) (b : B) (c : C) :
    (conjugationAction B C hn b c : G) = (b : G) * c * (b : G)⁻¹ := by rfl

omit [Finite G] in
/-- Enlarging the ambient actor enlarges its actual image. -/
theorem conjugationImage_mono {B D C : Subgroup G} (hBD : B ≤ D) :
    conjugationImage B C ≤ conjugationImage D C :=
  map_mono (subgroupOf_mono _ hBD)

omit [Finite G] in
/-- The full normalizer image is the range of the normalizer action. -/
theorem conjugationImage_normalizer (C : Subgroup G) :
    conjugationImage (normalizer (C : Set G)) C = C.normalizerMonoidHom.range := by
  rw [conjugationImage,subgroupOf_self,←MonoidHom.range_eq_map]

omit [Finite G] in
/-- The kernel is the actual centralizer inside the endpoint residual. -/
theorem conjugationAction_ker (B C : Subgroup G) (hn : B ≤ normalizer (C : Set G)) :
    (conjugationAction B C hn).ker = (centralizer (C : Set G)).subgroupOf B := by
  rw [conjugationAction,←MonoidHom.comap_ker,normalizerMonoidHom_ker]
  rfl

/-- A point residual acting on the common three-space has cubic or A₄
image. The cubic alternative is exactly centralization by its two-core. -/
theorem residual_image
    (B C Z : Subgroup G) [IsElementaryAbelian 2 C]
    (hp : IsPPerfect 2 B) (hc : Nat.card C = 8) (hz : Nat.card Z = 2)
    (hn : B ≤ normalizer (C : Set G))
    (hfixed : C ⊓ centralizer (B : Set G) = Z)
    (hquot : Nat.card (B ⧸ pCore 2 B) = 3) :
    (Nat.card (conjugationImage B C) = 3 ∨
      (Nat.card (conjugationImage B C) = 12 ∧ Nonempty (conjugationImage B C ≃* alternatingGroup (Fin 4)))) ∧
    (Nat.card (conjugationImage B C) = 3 ↔ B.pCoreIn 2 ≤ centralizer (C : Set G)) := by
  rw [conjugationImage_eq_range B C hn]
  let f := conjugationAction B C hn
  have hZC : Z ≤ C := hfixed ▸ inf_le_left
  have hZB : Z ≤ centralizer (B : Set G) := hfixed ▸ inf_le_right
  let : Nontrivial Z := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨z,hz1⟩ := exists_ne (1 : Z)
  let zC : C := ⟨z,hZC z.property⟩
  have hzC : zC ≠ 1 := fun he => hz1 (Subtype.ext (congrArg (fun x : C => (x : G)) he))
  have hfix (b : B) : f b zC = zC := by
    apply Subtype.ext
    change (b : G) * (z : G) * (b : G)⁻¹ = z
    rw [hZB z.property b b.property,mul_inv_cancel_right]
  have hone : Nat.card f.range ≠ 1 := by
    intro hh
    have he : f.range = ⊥ := f.range.eq_bot_iff_card.mpr hh
    have hBC : B ≤ centralizer (C : Set G) := by
      intro b hb
      have hk : (⟨b,hb⟩ : B) ∈ f.ker := he.le ⟨⟨b,hb⟩,rfl⟩
      exact (show (⟨b,hb⟩ : B) ∈ (centralizer (C : Set G)).subgroupOf B by
        rwa [←conjugationAction_ker B C hn])
    have heC : C = Z := by
      rw [←hfixed,inf_eq_left.mpr (le_centralizer_iff.mp hBC)]
    have hh := congrArg (fun D : Subgroup G => Nat.card D) heC
    rw [hc,hz] at hh
    omega
  have hd := (elementary_eight_twoPerfect_point_image hp hc f zC hzC hfix).resolve_left hone
  have hfp : IsPPerfect 2 f.range := hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  refine ⟨hd.imp_right (fun h12 => ⟨h12,twoPerfect_twelve_equiv_alternatingFour hfp h12⟩),?_⟩
  have hkernel : B.pCoreIn 2 ≤ centralizer (C : Set G) ↔ pCore 2 B ≤ f.ker := by
    rw [conjugationAction_ker]
    exact map_le_iff_le_comap
  rw [hkernel]
  constructor
  · intro h3
    have htwo : IsPGroup 2 ((pCore 2 B).map f.rangeRestrict) := pCore_isPGroup.map _
    have hdiv : Nat.card ((pCore 2 B).map f.rangeRestrict) ∣ 3 :=
      h3 ▸ ((pCore 2 B).map f.rangeRestrict).card_subgroup_dvd_card
    have hodd : Nat.Coprime 2 (Nat.card ((pCore 2 B).map f.rangeRestrict)) :=
      (by decide : Nat.Coprime 2 3).of_dvd_right hdiv
    have hbot : (pCore 2 B).map f.rangeRestrict = ⊥ := by
      apply eq_bot_iff.mpr
      intro a ha
      let v : (pCore 2 B).map f.rangeRestrict := ⟨a,ha⟩
      have hh := htwo.orderOf_coprime hodd v
      have hv : v = 1 := orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes hh dvd_rfl (orderOf_dvd_natCard v))
      exact congrArg (fun v : (pCore 2 B).map f.rangeRestrict => v.val) hv
    intro b hb
    have he := hbot.le (mem_map_of_mem f.rangeRestrict hb)
    exact congrArg Subtype.val he
  · intro hk
    let q : (B ⧸ pCore 2 B) →* f.range := QuotientGroup.lift _ f.rangeRestrict (fun b hb => Subtype.ext (hk hb))
    have hq : Function.Surjective q := by
      intro y
      obtain ⟨b,rfl⟩ := f.rangeRestrict_surjective y
      exact ⟨QuotientGroup.mk' _ b,rfl⟩
    have hdiv : Nat.card f.range ∣ 3 := hquot ▸ card_dvd_of_surjective q hq
    exact ((Nat.dvd_prime Nat.prime_three).mp hdiv).resolve_left hone

end Theory.GroupAction.ElementaryEightPointResidual
