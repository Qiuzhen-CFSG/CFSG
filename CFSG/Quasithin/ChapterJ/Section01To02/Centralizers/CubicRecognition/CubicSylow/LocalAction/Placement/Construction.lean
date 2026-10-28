module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.LocalAction.Placement.Transport
public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.StandardNormalizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Constructing the aligned cubic lift in J.2.7

The inverse of the supplied permutation conjugation aligns the literal marked
quotient map with the standard nine-group and its semidihedral complement.
The nine-group preimage is a Sylow three-subgroup. The complement preimage has
order 48 and contains the original involution z. Choose a Sylow two-subgroup
containing z there; its order 16 makes it Sylow in the full normalizer, of
order 432. Extending that Sylow to N_G(B) gives exactly the source's T_R.
The restricted marked map is injective by coprime orders and identifies T_R
with the actual coordinate complement, pointwise through its embedding.

The final two theorems establish the literal normalizer product and Sylow
placement for every Lift. Only the stated alignment is assumed; neither a
splitting nor centrality of the order-three kernel is required. The parent
source assembly must supply that alignment and the other J.2.7 premises.

Source: Aschbacher–Smith, J.2.7, printed p.437 (PDF p.448).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction.Placement
open Subgroup
open AlternatingSix.ShadowLocal
open AlternatingSix.M10.LocalGeometry
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

namespace Construction

/-- The original marking, followed by the inverse of the supplied conjugation. -/
def alignedMap (e : c.NormalizerQuotient ≃* AutA6) (σ : Equiv.Perm (Fin 6)) :
    c.NB →* AutA6 :=
  (MulAut.conj (permutationAction σ)).symm.toMonoidHom.comp (markedMap c e)

theorem alignedMap_surjective (e : c.NormalizerQuotient ≃* AutA6)
    (σ : Equiv.Perm (Fin 6)) : Function.Surjective (alignedMap c e σ) :=
  (MulAut.conj (permutationAction σ)).symm.surjective.comp (markedMap_surjective c e)

theorem alignedMap_ker (e : c.NormalizerQuotient ≃* AutA6) (σ : Equiv.Perm (Fin 6)) :
    (alignedMap c e σ).ker = c.normalizerKernel := by
  rw [alignedMap, MonoidHom.ker_comp_of_injective _ _
    (MulAut.conj (permutationAction σ)).symm.injective, markedMap_ker]

private theorem card_preimage (f : c.NB →* AutA6) (hf : Function.Surjective f)
    (U : Subgroup AutA6) : Nat.card (U.comap f) = Nat.card U * Nat.card f.ker := by
  let g := f.subgroupComap U
  have hg : Function.Surjective g := f.subgroupComap_surjective_of_surjective U hf
  have hk : g.ker = f.ker.subgroupOf (U.comap f) := by
    ext x
    change g x = 1 ↔ f x = 1
    exact Subtype.ext_iff
  rw [card_eq_card_quotient_mul_card_subgroup g.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv,
    hk, Nat.card_congr (subgroupOfEquivOfLe (ker_le_comap f U)).toEquiv]

private theorem model_normalizer_card :
    Nat.card (normalizer (AlternatingSix.M10.nine standardNine : Set AutA6)) = 144 := by
  rw [standardNormalizer_eq,
    card_sup_eq_mul_of_normalizes_of_disjoint _ _ standardComplement_le_normalizer
      standardComplement_disjoint,
    AlternatingSix.M10.Action.card_nine standardNine card_standardNine,
    card_standardComplement]

/-- The preimage of the standard nine-group under the aligned marking. -/
def R (hB : Nat.card c.B = 3) (e : c.NormalizerQuotient ≃* AutA6)
    (σ : Equiv.Perm (Fin 6)) : Sylow 3 c.NB :=
  AlternatingSix.M10.ThreeSylow.standard.comapOfKerIsPGroup (alignedMap c e σ)
    (IsPGroup.of_card (n := 1) (by
      rw [alignedMap_ker, normalizerKernel_card c hB, pow_one]))
    (by rw [MonoidHom.range_eq_top.mpr (alignedMap_surjective c e σ)]; exact le_top)

theorem R_image (hB : Nat.card c.B = 3) (e : c.NormalizerQuotient ≃* AutA6)
    (σ : Equiv.Perm (Fin 6)) :
    (R c hB e σ : Subgroup c.NB).map (markedMap c e) =
      (AlternatingSix.M10.nine standardNine).map
        (MulAut.conj (permutationAction σ)).toMonoidHom := by
  have hf : markedMap c e = (MulAut.conj (permutationAction σ)).toMonoidHom.comp
      (alignedMap c e σ) := by
    apply MonoidHom.ext
    intro x
    exact ((MulAut.conj (permutationAction σ)).apply_symm_apply _).symm
  rw [hf, ← map_map]
  congr 1
  exact map_comap_eq_self_of_surjective (alignedMap_surjective c e σ) _

/-- The source normalizer, with both conditions in the original ambient group. -/
def normalizerIn (R : Sylow 3 c.NB) : Subgroup G :=
  c.NB ⊓ normalizer (ambient c R : Set G)

theorem normalizerIn_eq (R : Sylow 3 c.NB) :
    normalizerIn c R = (normalizer (R : Set c.NB)).map c.NB.subtype := by
  change c.NB ⊓ normalizer (ambient c R : Set G) = _
  calc
    _ = ((normalizer (ambient c R : Set G)).comap c.NB.subtype).map c.NB.subtype := by
      rw [map_comap_eq, c.NB.range_subtype]
    _ = _ := by
      rw [comap_normalizer_eq_of_le_range
        ((ambient_le_NB c R).trans_eq c.NB.range_subtype.symm),
        ambient, comap_map_eq_self_of_injective c.NB.subtype_injective]
      rfl

private theorem normalizer_card_of_image (hB : Nat.card c.B = 3)
    (e : c.NormalizerQuotient ≃* AutA6) (σ : Equiv.Perm (Fin 6))
    (R : Sylow 3 c.NB)
    (hR : (R : Subgroup c.NB).map (markedMap c e) =
      (AlternatingSix.M10.nine standardNine).map
        (MulAut.conj (permutationAction σ)).toMonoidHom) :
    Nat.card (normalizer (R : Set c.NB)) = 432 := by
  have hr : (R : Subgroup c.NB) = ((R : Subgroup c.NB).map (markedMap c e)).comap
      (markedMap c e) := (comap_map_eq_self (by
        rw [markedMap_ker]; exact kernel_le c hB R)).symm
  change Nat.card (normalizer ((R : Subgroup c.NB) : Set c.NB)) = 432
  conv_lhs => rw [hr]
  rw [← comap_normalizer_eq_of_surjective _ (markedMap_surjective c e),
    card_preimage c _ (markedMap_surjective c e), markedMap_ker,
    normalizerKernel_card c hB, hR, ← map_equiv_normalizer_eq,
    card_map_of_injective (MulAut.conj (permutationAction σ)).injective,
    model_normalizer_card]

theorem normalizerIn_card (hB : Nat.card c.B = 3)
    (e : c.NormalizerQuotient ≃* AutA6) (σ : Equiv.Perm (Fin 6))
    (l : Lift c e σ) : Nat.card (normalizerIn c l.R) = 432 := by
  rw [normalizerIn_eq, card_map_of_injective c.NB.subtype_injective]
  exact normalizer_card_of_image c hB e σ l.R l.image_R

/-- Choose an actual complement above the model complement, retaining z. -/
private theorem exists_complement_above (hB : Nat.card c.B = 3)
    (hz : orderOf c.z = 2) (e : c.NormalizerQuotient ≃* AutA6)
    (σ : Equiv.Perm (Fin 6))
    (hσ : markedMap c e (zInNB c) =
      (MulAut.conj (permutationAction σ)) (permutationAction (standardU * standardZ))) :
    ∃ W : Subgroup c.NB, W ≤ standardComplement.comap (alignedMap c e σ) ∧
      Nat.card W = 16 ∧ zInNB c ∈ W ∧
      ∃ a : W ≃* Coordinates.complement,
        ∀ w : W, alignedMap c e σ w = Identification.embedding (a w) := by
  let f := alignedMap c e σ
  let Q := standardComplement.comap f
  have hQcard : Nat.card Q = 48 := by
    rw [card_preimage c f (alignedMap_surjective c e σ), card_standardComplement]
    change 16 * Nat.card (alignedMap c e σ).ker = 48
    rw [alignedMap_ker, normalizerKernel_card c hB]
  have hzQ : zInNB c ∈ Q := by
    change (MulAut.conj (permutationAction σ)).symm (markedMap c e (zInNB c)) ∈
      standardComplement
    rw [hσ, MulEquiv.symm_apply_apply, ← embedding_central]
    exact mem_map_of_mem _ (Coordinates.complement.pow_mem Coordinates.rotation_mem 4)
  let zQ : Q := ⟨zInNB c, hzQ⟩
  have hzQo : orderOf zQ = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact zInNB_order c hz
  obtain ⟨S, hS⟩ := (IsPGroup.of_card (p := 2) (G := zpowers zQ) (n := 1)
    (by rw [Nat.card_zpowers, hzQo, pow_one])).exists_le_sylow
  let W : Subgroup c.NB := (S : Subgroup Q).map Q.subtype
  have hWcard : Nat.card W = 16 := by
    rw [card_map_of_injective Q.subtype_injective, S.card_eq_multiplicity, hQcard]
    decide +kernel
  have hWQ : W ≤ Q := map_subtype_le _
  let g : W →* standardComplement := f.restrict hWQ
  have hd : Disjoint f.ker W := disjoint_of_coprime_natCard (by
    rw [show f.ker = c.normalizerKernel from alignedMap_ker c e σ,
      normalizerKernel_card c hB, hWcard]
    decide)
  have hg : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff g).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    exact disjoint_def.mp hd (congrArg Subtype.val (show g x = 1 from hx)) x.property
  have hg' : Function.Bijective g := (Nat.bijective_iff_injective_and_card g).mpr
    ⟨hg, by rw [hWcard, card_standardComplement]⟩
  let b : W ≃* standardComplement := MulEquiv.ofBijective g hg'
  let j : Coordinates.complement ≃* standardComplement :=
    Coordinates.complement.equivMapOfInjective Identification.embedding
      Identification.embedding_injective
  refine ⟨W, hWQ, hWcard, mem_map_of_mem Q.subtype (hS (mem_zpowers zQ)),
    b.trans j.symm, ?_⟩
  intro w
  exact (congrArg Subtype.val (j.apply_symm_apply (b w))).symm

/-- Construct the literal aligned lift; no splitting or placement witness is an input. -/
theorem exists_lift (hB : Nat.card c.B = 3) (hz : orderOf c.z = 2)
    (e : c.NormalizerQuotient ≃* AutA6) (σ : Equiv.Perm (Fin 6))
    (hσ : markedMap c e (zInNB c) =
      (MulAut.conj (permutationAction σ)) (permutationAction (standardU * standardZ))) :
    Nonempty (Lift c e σ) := by
  let r := R c hB e σ
  let N := normalizer (r : Set c.NB)
  obtain ⟨W, hWQ, hWcard, hzW, a, ha⟩ := exists_complement_above c hB hz e σ hσ
  have hWN : W ≤ N := by
    apply hWQ.trans
    exact (comap_mono standardComplement_le_normalizer).trans
      ((AlternatingSix.M10.nine standardNine).le_normalizer_comap (alignedMap c e σ))
  have hNcard : Nat.card N = 432 := normalizer_card_of_image c hB e σ r (R_image c hB e σ)
  let S : Sylow 2 N := Sylow.ofCard (W.subgroupOf N) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv, hWcard, hNcard]
    decide +kernel)
  obtain ⟨Tplus, hTplus⟩ := S.exists_comap_subtype_eq
  have hTW : (Tplus : Subgroup c.NB) ⊓ N = W := by
    have hh := congrArg (Subgroup.map N.subtype) hTplus
    change ((Tplus : Subgroup c.NB).subgroupOf N).map N.subtype =
      (W.subgroupOf N).map N.subtype at hh
    rwa [subgroupOf_map_subtype, map_subgroupOf_eq_of_le hWN] at hh
  have hTR : TR c r Tplus = W.map c.NB.subtype := by
    have hnorm : (normalizer (ambient c r : Set G)).comap c.NB.subtype = N := by
      rw [comap_normalizer_eq_of_le_range ((ambient_le_NB c r).trans_eq c.NB.range_subtype.symm),
        ambient, comap_map_eq_self_of_injective c.NB.subtype_injective]
      rfl
    have hi : (TR c r Tplus).comap c.NB.subtype = W := by
      rw [TR, comap_inf, twoAmbient,
        comap_map_eq_self_of_injective c.NB.subtype_injective, hnorm, hTW]
    have hm := congrArg (Subgroup.map c.NB.subtype) hi
    rwa [map_comap_eq, c.NB.range_subtype, inf_eq_right.mpr (TR_le_NB c r Tplus)] at hm
  let b : TR c r Tplus ≃* W := (MulEquiv.subgroupCongr hTR).trans
    (W.equivMapOfInjective c.NB.subtype c.NB.subtype_injective).symm
  have hb (t : TR c r Tplus) : ((b t : c.NB) : G) = t := by
    have hh := congrArg Subtype.val
      ((W.equivMapOfInjective c.NB.subtype c.NB.subtype_injective).apply_symm_apply
        ((MulEquiv.subgroupCongr hTR) t))
    exact hh
  refine ⟨⟨r, Tplus, b.trans a, ?_, R_image c hB e σ, ?_⟩⟩
  · intro t
    apply (MulAut.conj (permutationAction σ)).symm.injective
    rw [MulEquiv.symm_apply_apply]
    change alignedMap c e σ _ = Identification.embedding (a (b t))
    rw [← ha]
    congr 1
    exact Subtype.ext (hb t).symm
  · rw [hTR]
    exact mem_map_of_mem c.NB.subtype hzW

/-- A chosen lift with the original Sylow subgroups and marked quotient map. -/
def lift (hB : Nat.card c.B = 3) (hz : orderOf c.z = 2)
    (e : c.NormalizerQuotient ≃* AutA6) (σ : Equiv.Perm (Fin 6))
    (hσ : markedMap c e (zInNB c) =
      (MulAut.conj (permutationAction σ)) (permutationAction (standardU * standardZ))) :
    Lift c e σ := Classical.choice (exists_lift c hB hz e σ hσ)

end Construction

namespace Lift
variable {c} {e : c.NormalizerQuotient ≃* AutA6} {σ : Equiv.Perm (Fin 6)}
variable (l : Lift c e σ)

/-- The literal setwise product in the source, retaining both actual factors. -/
theorem normalizer_product (hB : Nat.card c.B = 3) (x : G) :
    x ∈ c.NB ⊓ normalizer (ambient c l.R : Set G) ↔
      ∃ a ∈ ambient c l.R, ∃ t ∈ TR c l.R l.Tplus, a * t = x := by
  have hn := TR_le_normalizer c l.R l.Tplus
  have he : ambient c l.R ⊔ TR c l.R l.Tplus = Construction.normalizerIn c l.R := by
    apply eq_of_le_of_card_ge
    · exact sup_le (le_inf (ambient_le_NB c l.R) (ambient c l.R).le_normalizer)
        (le_inf (TR_le_NB c l.R l.Tplus) hn)
    · rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn
        ((ambient_isPGroup c l.R).disjoint_of_coprime
          (TR_isPGroup c l.R l.Tplus) (by decide)),
        ambient_card c hB e, l.card, Construction.normalizerIn_card c hB e σ l]
  change x ∈ Construction.normalizerIn c l.R ↔ _
  rw [← he]
  exact Set.ext_iff.mp
    (coe_mul_of_right_le_normalizer_left (ambient c l.R) (TR c l.R l.Tplus) hn) x

/-- The source's T_R is the actual image of a Sylow two-subgroup of its normalizer. -/
theorem exists_sylow_two (hB : Nat.card c.B = 3) :
    ∃ S : Sylow 2 ↥(c.NB ⊓ normalizer (ambient c l.R : Set G)),
      (S : Subgroup ↥(c.NB ⊓ normalizer (ambient c l.R : Set G))).map
        (c.NB ⊓ normalizer (ambient c l.R : Set G)).subtype = TR c l.R l.Tplus := by
  have hle : TR c l.R l.Tplus ≤ Construction.normalizerIn c l.R :=
    le_inf (TR_le_NB c l.R l.Tplus) (TR_le_normalizer c l.R l.Tplus)
  let S : Sylow 2 (Construction.normalizerIn c l.R) :=
    Sylow.ofCard ((TR c l.R l.Tplus).subgroupOf (Construction.normalizerIn c l.R)) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
        l.card, Construction.normalizerIn_card c hB e σ l]
      decide +kernel)
  exact ⟨S, map_subgroupOf_eq_of_le hle⟩

end Lift
end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction.Placement
