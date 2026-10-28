module
public import Theory.GroupAction.ElementaryEightPointResidual.Enlargement
public import Theory.GroupTheory.ElementaryEightThreeNormalizer
public import Mathlib.GroupTheory.Sylow

/-!
# Point images with an ambient Sylow index two

If R has index two in an ambient Sylow two-subgroup and lies in an actor
surjecting onto GL₃(2), its image has order divisible by four. It cannot
normalize a cubic subgroup of GL₃(2), whose normalizer has two-part at most
two. Thus a normalized point residual with cubic-or-A₄ image has image A₄.

An A₄ point image is normal in the point stabilizer of order twenty-four.
Its normalizer therefore has odd index in GL₃(2). Taking the full preimage
inside a specified normal covering subgroup constructs the literal L₀ and
a Sylow subgroup of the actor normalizing it and containing the given R.
The entire action kernel in the cover is retained; no identification with
the cover's two-core is used.

Source application: Aschbacher–Smith 14.7.6, printed pp.1044–1045,
refs/quasithin.pdf; LocalReduction.LargePrimePointLiftSource applies these
statements to the original selected common eight-group and factor normalizer.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupAction.ElementaryEightPointResidual
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The public action equations identify the image with the literal normalizer map. -/
theorem conjugationImage_eq_map_of_le (B C : Subgroup G) (hn : B ≤ normalizer (C : Set G)) :
    conjugationImage B C = (B.subgroupOf (normalizer (C : Set G))).map C.normalizerMonoidHom := by
  rw [conjugationImage_eq_range B C hn]
  have he (b : B) : conjugationAction B C hn b = C.normalizerMonoidHom ⟨b,hn b.property⟩ := by
    ext c
    exact conjugationAction_apply B C hn b c
  ext a
  constructor
  · rintro ⟨b,rfl⟩
    exact ⟨⟨b,hn b.property⟩,b.property,(he b).symm⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨⟨b,hb⟩,he ⟨b,hb⟩⟩

omit [Finite G] in
/-- Normalization of the actual actors passes to their literal images. -/
theorem conjugationImage_normalizes
    (R B C : Subgroup G) (hRC : R ≤ normalizer (C : Set G))
    (hBC : B ≤ normalizer (C : Set G)) (hRB : R ≤ normalizer (B : Set G)) :
    conjugationImage R C ≤ normalizer (conjugationImage B C : Set (MulAut C)) := by
  rw [conjugationImage_eq_map_of_le R C hRC,conjugationImage_eq_map_of_le B C hBC]
  apply (map_mono (show R.subgroupOf (normalizer (C : Set G)) ≤
    normalizer (B.subgroupOf (normalizer (C : Set G)) : Set (normalizer (C : Set G))) from ?_)).trans
    ((B.subgroupOf (normalizer (C : Set G))).le_normalizer_map C.normalizerMonoidHom)
  intro r hr
  apply mem_normalizer_iff.mpr
  intro b
  change (b : G) ∈ B ↔ (r : G) * (b : G) * (r : G)⁻¹ ∈ B
  exact mem_normalizer_iff.mp (hRB hr) b

private theorem image_four_dvd
    (S : Sylow 2 G) (R N : Subgroup G)
    (hRS : R ≤ S) (hi : R.relIndex (S : Subgroup G) = 2) (hRN : R ≤ N)
    {E : Type*} [Group E] [Finite E]
    (f : N →* E) (hf : Function.Surjective f) (hE : 8 ∣ Nat.card E) :
    4 ∣ Nat.card ((R.subgroupOf N).map f) := by
  let A := (R.subgroupOf N).map f
  have hind : A.index ∣ 2 * (S : Subgroup G).index := by
    have hd := ((R.subgroupOf N).index_map_dvd hf).trans (relIndex_dvd_index_of_le hRN)
    rwa [←relIndex_mul_index hRS,hi] at hd
  have hd : 8 ∣ Nat.card A * (2 * (S : Subgroup G).index) :=
    hE.trans (by rw [←A.card_mul_index]; exact Nat.mul_dvd_mul_left _ hind)
  have hc : Nat.Coprime 8 (S : Subgroup G).index :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr S.not_dvd_index).pow_left 3
  have hd' : 8 ∣ 2 * Nat.card A := hc.dvd_of_dvd_mul_right (by
    convert hd using 1
    ring)
  exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hd'

/-- Full common-space action and the original Sylow index exclude a cubic
point image; the original point residual, rather than an abstract A4, is retained. -/
theorem twelve_of_full_action_of_sylow_index_two
    (S : Sylow 2 G) (R B C : Subgroup G) [IsElementaryAbelian 2 C]
    (hRS : R ≤ S) (hi : R.relIndex (S : Subgroup G) = 2)
    (hRC : R ≤ normalizer (C : Set G))
    (hBC : B ≤ normalizer (C : Set G))
    (hRB : R ≤ normalizer (B : Set G)) (hc : Nat.card C = 8)
    (hfull : conjugationImage (normalizer (C : Set G)) C = ⊤)
    (halt : Nat.card (conjugationImage B C) = 3 ∨ Nat.card (conjugationImage B C) = 12) :
    Nat.card (conjugationImage B C) = 12 := by
  refine halt.resolve_left ?_
  intro hthree
  have hsurj : Function.Surjective C.normalizerMonoidHom :=
    MonoidHom.range_eq_top.mp ((conjugationImage_normalizer C).symm.trans hfull)
  have hfour : 4 ∣ Nat.card (conjugationImage R C) := by
    rw [conjugationImage_eq_map_of_le R C hRC]
    exact image_four_dvd S R _ hRS hi hRC C.normalizerMonoidHom hsurj
      (by rw [card_mulAut_of_elementary_eight C hc]; decide)
  have hnorm := conjugationImage_normalizes R B C hRC hBC hRB
  exact not_four_dvd_card_normalizer_of_elementary_eight_three hc _ hthree
    (hfour.trans (card_dvd_of_le hnorm))

private theorem odd_index_normalizer_twelve
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (B : Subgroup (MulAut E))
    (hB : Nat.card B = 12) (z : E) (hz : z ≠ 1)
    (hfix : ∀ b : B, (b : MulAut E) z = z) :
    Odd (normalizer (B : Set (MulAut E))).index := by
  let A := MulAction.stabilizer (MulAut E) z
  have hBA : B ≤ A := fun b hb => hfix ⟨b,hb⟩
  have hA : Nat.card A = 24 := (full_point_stabilizer hE z hz).1
  have hBi : (B.subgroupOf A).index = 2 := by
    have hh := (B.subgroupOf A).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv,hB,hA] at hh
    omega
  have hn : A ≤ normalizer (B : Set (MulAut E)) :=
    (normal_subgroupOf_iff_le_normalizer hBA).mp (normal_of_index_eq_two hBi)
  have hi : A.index = 7 := by
    have hh := A.card_mul_index
    rw [hA,card_mulAut_of_elementary_eight E hE] at hh
    omega
  exact Odd.of_dvd_nat (by decide : Odd 7) (hi ▸ index_dvd_of_le hn)

/-- An order-twelve point image has a full preimage inside the same normal
cover. A Sylow subgroup of the ambient actor normalizes this preimage and
contains the prescribed two-subgroup. The complete action kernel is retained. -/
theorem exists_sylow_normalizing_twelve_preimage
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (f : G →* MulAut E) (hf : Function.Surjective f)
    (D : Subgroup G) [D.Normal] (hD : D.map f = ⊤)
    (B : Subgroup (MulAut E)) (hB : Nat.card B = 12)
    (z : E) (hz : z ≠ 1) (hfix : ∀ b : B, (b : MulAut E) z = z)
    (R : Subgroup G) (hR : IsPGroup 2 R)
    (hRB : R.map f ≤ normalizer (B : Set (MulAut E))) :
    let L0 := D ⊓ B.comap f
    L0.map f = B ∧ D ⊓ f.ker ≤ L0 ∧
      ∃ P : Sylow 2 G, R ≤ P ∧ (P : Subgroup G) ≤ normalizer (L0 : Set G) := by
  let L0 := D ⊓ B.comap f
  have hm : L0.map f = B := by
    apply le_antisymm
    · rintro _ ⟨g,hg,rfl⟩
      exact hg.2
    · intro b hb
      obtain ⟨g,hg,hgb⟩ := hD.ge (mem_top b)
      exact ⟨g,⟨hg,by change f g ∈ B; rwa [hgb]⟩,hgb⟩
  have hk : D ⊓ f.ker ≤ L0 := inf_le_inf_left _ (by
    intro x hx
    change f x ∈ B
    rw [show f x = 1 from hx]
    exact B.one_mem)
  let M := (normalizer (B : Set (MulAut E))).comap f
  have hi : Odd M.index := by
    rw [show M.index = (normalizer (B : Set (MulAut E))).index from
      index_comap_of_surjective _ hf]
    exact odd_index_normalizer_twelve hE B hB z hz hfix
  have hRM : R ≤ M := map_le_iff_le_comap.mp hRB
  have hML : M ≤ normalizer (L0 : Set G) :=
    (le_inf le_normalizer_of_normal (B.le_normalizer_comap f)).trans inf_normalizer_le_normalizer_inf
  obtain ⟨P,hP⟩ := (hR.comap_subtype (K := M)).exists_le_sylow
  let P0 := (P : Subgroup M).map M.subtype
  have hPi : ¬ 2 ∣ P0.index := by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index hi.not_two_dvd_nat
  let Q : Sylow 2 G := (P.isPGroup'.map M.subtype).toSylow hPi
  refine ⟨hm,hk,Q,?_,(map_subtype_le _).trans hML⟩
  change R ≤ P0
  rw [←map_subgroupOf_eq_of_le hRM]
  exact map_mono hP

/-- In the full-action branch, the original index-two factor normalizer
forces the original point image to be A4. Its full preimage in the same
normal component has a compatible Sylow normalizer in N_G(C). -/
theorem point_preimage_sylow
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (R B C Z : Subgroup G) [IsElementaryAbelian 2 C]
    (hRS : R ≤ S) (hi : R.relIndex (S : Subgroup G) = 2)
    (hRC : R ≤ normalizer (C : Set G))
    (hBC : B ≤ normalizer (C : Set G))
    (hRB : R ≤ normalizer (B : Set G))
    (hc : Nat.card C = 8) (hz : Nat.card Z = 2)
    (hfixed : C ⊓ centralizer (B : Set G) = Z)
    (halt : Nat.card (conjugationImage B C) = 3 ∨
      (Nat.card (conjugationImage B C) = 12 ∧
        Nonempty (conjugationImage B C ≃* alternatingGroup (Fin 4))))
    (D : Subgroup (normalizer (C : Set G))) [D.Normal]
    (hD : D.map C.normalizerMonoidHom = ⊤) :
    Nat.card (conjugationImage B C) = 12 ∧
      Nonempty (conjugationImage B C ≃* alternatingGroup (Fin 4)) ∧
      let L0 := D ⊓ (conjugationImage B C).comap C.normalizerMonoidHom
      let L0G := L0.map (normalizer (C : Set G)).subtype
      conjugationImage L0G C = conjugationImage B C ∧
      (D ⊓ C.normalizerMonoidHom.ker).map (normalizer (C : Set G)).subtype ≤ L0G ∧
      ∃ P : Sylow 2 (normalizer (C : Set G)),
        R ≤ (P : Subgroup (normalizer (C : Set G))).map (normalizer (C : Set G)).subtype ∧
        (P : Subgroup (normalizer (C : Set G))).map (normalizer (C : Set G)).subtype ≤
          normalizer (L0G : Set G) := by
  let N := normalizer (C : Set G)
  have hf : Function.Surjective C.normalizerMonoidHom := by
    intro a
    obtain ⟨x,_,hx⟩ := hD.ge (mem_top a)
    exact ⟨x,hx⟩
  have hfull : conjugationImage N C = ⊤ :=
    (conjugationImage_normalizer C).trans (MonoidHom.range_eq_top.mpr hf)
  have h12 := twelve_of_full_action_of_sylow_index_two S R B C hRS hi hRC hBC hRB hc hfull
    (halt.imp_right And.left)
  have he := (halt.resolve_left (by omega)).2
  obtain ⟨z,hz1,_⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hz
  have hZC : Z ≤ C := hfixed ▸ inf_le_left
  let zC : C := ⟨z,hZC z.property⟩
  have hzC : zC ≠ 1 := fun he => hz1 (Subtype.ext (congrArg (fun c : C => (c : G)) he))
  have hfix : ∀ b : conjugationImage B C, (b : MulAut C) zC = zC := by
    apply (fixed_by_conjugationImage_iff B C hBC zC).mpr
    exact (show (z : G) ∈ C ⊓ centralizer (B : Set G) from hfixed.symm ▸ z.property).2
  have hnorm := conjugationImage_normalizes R B C hRC hBC hRB
  rw [conjugationImage_eq_map_of_le R C hRC] at hnorm
  obtain ⟨hm,hk,P,hRP,hPN⟩ := exists_sylow_normalizing_twelve_preimage hc
    C.normalizerMonoidHom hf D hD (conjugationImage B C) h12 zC hzC hfix
    (R.subgroupOf N) ((S.isPGroup'.to_le hRS).comap_subtype) hnorm
  refine ⟨h12,he,?_,map_mono hk,P,?_,?_⟩
  · rw [conjugationImage_eq_map_of_le _ C (map_subtype_le _)]
    change (((D ⊓ (conjugationImage B C).comap C.normalizerMonoidHom).map N.subtype).comap
      N.subtype).map C.normalizerMonoidHom = _
    rw [comap_map_eq_self_of_injective N.subtype_injective]
    exact hm
  · rw [←map_subgroupOf_eq_of_le hRC]
    exact map_mono hRP
  · exact (map_mono hPN).trans ((D ⊓ (conjugationImage B C).comap C.normalizerMonoidHom).le_normalizer_map N.subtype)

end Theory.GroupAction.ElementaryEightPointResidual
