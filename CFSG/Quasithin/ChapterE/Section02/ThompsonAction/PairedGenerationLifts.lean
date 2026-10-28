module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedImages
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairResidual

/-!
# Genuine elementary lifts for the two natural source factors

A moving maximum elementary subgroup has an offender image on the natural
quotient. Product splitting puts a full coordinate Sylow in that image.
Intersecting the original elementary subgroup with its inverse image gives
a genuine elementary lift; the prescribed Sylow exchanger gives the other.
The original centralizer quotient and both coordinate inclusions are retained.
This supplies the elementary-lift premise of the paired E-generation obstruction.
Source: Aschbacher--Smith B.2.7, B.6.10 and E.2.3, pp.76,117,216--217.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction.PairGeneration
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "V" => Fin 2 → F

omit [Algebra (ZMod 2) F] in
theorem sylow_pair (Y : Subgroup H) [Y.Normal] (e : Y ≃* D × D)
    (S : Sylow 2 H) : ∃ P Q : Sylow 2 D,
      (S : Subgroup H) ⊓ Y =
        ((P : Subgroup D).prod Q).map (Y.subtype.comp e.symm.toMonoidHom) := by
  obtain ⟨R,hR⟩ := S.exists_sylow_map_eq_inf_of_normal Y
  let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let P := R'.mapSurjective (f := MonoidHom.fst D D) (fun g => ⟨(g,1),rfl⟩)
  let Q := R'.mapSurjective (f := MonoidHom.snd D D) (fun g => ⟨(1,g),rfl⟩)
  have hp : IsPGroup 2 (P × Q) := by
    obtain ⟨m,hm⟩ := P.isPGroup'.exists_card_eq
    obtain ⟨n,hn⟩ := Q.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := m+n) (by rw [Nat.card_prod,hm,hn,pow_add])
  have hPQ : (R : Subgroup Y).map e.toMonoidHom = (P : Subgroup D).prod Q := by
    apply (R'.is_maximal' (hp.of_equiv ((P : Subgroup D).prodEquiv (Q : Subgroup D)).symm) ?_).symm
    intro x hx
    exact ⟨mem_map_of_mem (MonoidHom.fst D D) hx,mem_map_of_mem (MonoidHom.snd D D) hx⟩
  refine ⟨P,Q,?_⟩
  rw [←hR,←hPQ,Subgroup.map_map]
  congr 1
  ext x
  simp

omit [Finite G] [Finite H] in
private theorem elementary_subimage (q : G →* H) (T : Subgroup G)
    (B : Subgroup G) [IsElementaryAbelian 2 B] (hBT : B ≤ T)
    (E : Subgroup H) (hE : E ≤ B.map q) :
    ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ A ≤ T ∧ A.map q = E := by
  let A := B ⊓ E.comap q
  refine ⟨A,IsElementaryAbelian.of_le (show A ≤ B from inf_le_left),
    inf_le_left.trans hBT,le_antisymm ?_ ?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact hx.2
  · intro x hx
    obtain ⟨b,hb,rfl⟩ := hE hx
    exact ⟨b,⟨hb,hx⟩,rfl⟩

omit [Finite G] [Finite H] in
private theorem conjugate_elementary_lift (q : G →* H) (T : Subgroup G)
    (E E' : Subgroup H) (g : G) (hg : g ∈ T)
    (he : E.map (MulAut.conj (q g)).toMonoidHom = E')
    (hl : ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ A ≤ T ∧ A.map q = E) :
    ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ A ≤ T ∧ A.map q = E' := by
  obtain ⟨A,ha,hAT,hA⟩ := hl
  let := ha
  refine ⟨A.map (MulAut.conj g).toMonoidHom,IsElementaryAbelian.map _,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact T.mul_mem (T.mul_mem hg (hAT hx)) (T.inv_mem hg)
  · rw [map_map]
    have hc : q.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (q g)).toMonoidHom.comp q := by
      ext x
      simp [MulAut.conj_apply]
    rw [hc,←map_map,hA,he]

theorem paired_elementary_lifts
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G)) (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (Y : Subgroup H) [Y.Normal] (e : Y ≃* D × D)
    (f : Additive U →ₗ[ZMod 2] (V × V)) (hf : Function.Surjective f)
    (he : ∀ (g : Y) v, f (NormalElementaryQuotient.representation U q hq hk (g : H) v) =
      SL2NaturalOffenders.naturalPair (F := F) (e g) (f v))
    (hY : offenderSubgroup (NormalElementaryQuotient.representation U q hq hk) ≤ Y)
    (P Q : Sylow 2 D)
    (hPQ : (T : Subgroup G).map q ⊓ Y =
      ((P : Subgroup D).prod Q).map (Y.subtype.comp e.symm.toMonoidHom))
    (hex : ∃ t ∈ (T : Subgroup G),
      ((((⊤ : Subgroup D).prod ⊥).map (Y.subtype.comp e.symm.toMonoidHom)).map
        (MulAut.conj (q t)).toMonoidHom =
          ((⊥ : Subgroup D).prod ⊤).map (Y.subtype.comp e.symm.toMonoidHom)) ∧
      ((((⊥ : Subgroup D).prod ⊤).map (Y.subtype.comp e.symm.toMonoidHom)).map
        (MulAut.conj (q t)).toMonoidHom =
          ((⊤ : Subgroup D).prod ⊥).map (Y.subtype.comp e.symm.toMonoidHom))) :
    (∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ A ≤ T ∧
      A.map q = ((P : Subgroup D).prod ⊥).map (Y.subtype.comp e.symm.toMonoidHom)) ∧
    (∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ A ≤ T ∧
      A.map q = ((⊥ : Subgroup D).prod Q).map (Y.subtype.comp e.symm.toMonoidHom)) := by
  let α := NormalElementaryQuotient.representation U q hq hk
  let η : D × D →* H := Y.subtype.comp e.symm.toMonoidHom
  have hη : Function.Injective η := Y.subtype_injective.comp e.symm.injective
  have hJT := RankOneBaumann.thompson_image_le_offender_layer T U q hq hk hUT Y hY
  have hexB : ∃ B ∈ elementaryAbelianMaxSubgroups (T : Subgroup G), B.map q ≠ ⊥ := by
    by_contra! hn
    apply hJ
    rw [←hk]
    exact sSup_le fun B hB => (map_eq_bot_iff B).mp (hn B hB)
  obtain ⟨B,hB,hb⟩ := hexB
  let : IsElementaryAbelian 2 B := hB.2.1
  have hBL : B.map q ≤ Y := (map_mono (le_sSup hB)).trans hJT
  have hBoff : IsOffender α (B.map q) :=
    (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
      U q hq hk (T : Subgroup G) B hUT hB hb).isOffender α
  let B₀ := ((B.map q).subgroupOf Y).map e.toMonoidHom
  have hB₀map : B₀.map η = B.map q := by
    rw [show B₀ = ((B.map q).subgroupOf Y).map e.toMonoidHom from rfl,map_map]
    have hh : η.comp e.toMonoidHom = Y.subtype := by ext x; simp [η]
    rw [hh,map_subgroupOf_eq_of_le hBL]
  have hB₀off : IsOffender (SL2NaturalOffenders.naturalPair (F := F)) B₀ := by
    have hc := fixedCodim_le_of_equivariant_surjection (α.comp Y.subtype)
      ((SL2NaturalOffenders.naturalPair (F := F)).comp e.toMonoidHom) f hf he
      ((B.map q).subgroupOf Y)
    have ho := hBoff.subgroupOf α hBL
    exact (IsOffender.map_equivariant ((SL2NaturalOffenders.naturalPair (F := F)).comp e.toMonoidHom)
      (SL2NaturalOffenders.naturalPair (F := F)) e.toMonoidHom e.injective
      (LinearEquiv.refl (ZMod 2) _) (fun _ _ => rfl) ⟨ho.1,hc.trans ho.2⟩)
  have hB₀le : B₀ ≤ (P : Subgroup D).prod Q := by
    intro x hx
    have hy : η x ∈ B.map q := hB₀map ▸ mem_map_of_mem η hx
    have hh : η x ∈ (T : Subgroup G).map q ⊓ Y :=
      ⟨map_mono hB.1 hy,hBL hy⟩
    rw [hPQ] at hh
    obtain ⟨y,hy,hxy⟩ := hh
    exact hη hxy ▸ hy
  have haxis := RankOneBaumann.pair_offender_contains_axis P Q B₀ hB₀off hB₀le
  have h₁ : (T : Subgroup G).map q ⊓ (((⊤ : Subgroup D).prod ⊥).map η) =
      ((P : Subgroup D).prod ⊥).map η := by
    have hle : ((⊤ : Subgroup D).prod ⊥).map η ≤ Y := by
      rintro _ ⟨x,_,rfl⟩; exact (e.symm x).property
    have hh := inf_assoc ((T : Subgroup G).map q) Y (((⊤ : Subgroup D).prod ⊥).map η)
    rw [inf_of_le_right hle] at hh
    rw [←hh,hPQ,←Subgroup.map_inf _ _ η hη]
    congr 1
    ext x
    simp only [mem_inf,mem_prod,mem_top,mem_bot]
    constructor
    · tauto
    · rintro ⟨h,hx⟩; exact ⟨⟨h,hx ▸ Q.one_mem⟩,trivial,hx⟩
  have h₂ : (T : Subgroup G).map q ⊓ (((⊥ : Subgroup D).prod ⊤).map η) =
      ((⊥ : Subgroup D).prod Q).map η := by
    have hle : ((⊥ : Subgroup D).prod ⊤).map η ≤ Y := by
      rintro _ ⟨x,_,rfl⟩; exact (e.symm x).property
    have hh := inf_assoc ((T : Subgroup G).map q) Y (((⊥ : Subgroup D).prod ⊤).map η)
    rw [inf_of_le_right hle] at hh
    rw [←hh,hPQ,←Subgroup.map_inf _ _ η hη]
    congr 1
    ext x
    simp only [mem_inf,mem_prod,mem_top,mem_bot]
    constructor
    · tauto
    · rintro ⟨hx,h⟩; exact ⟨⟨hx ▸ P.one_mem,h⟩,hx,trivial⟩
  obtain ⟨t,ht,ht₁,ht₂⟩ := hex
  have hT : ((T : Subgroup G).map q).map (MulAut.conj (q t)).toMonoidHom =
      (T : Subgroup G).map q := by
    rw [map_map]
    have hc : (MulAut.conj (q t)).toMonoidHom.comp q = q.comp (MulAut.conj t).toMonoidHom := by
      ext x; simp [MulAut.conj_apply]
    have hTmap : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
    rw [hc,←map_map,hTmap]
  have hE₁ : (((P : Subgroup D).prod ⊥).map η).map (MulAut.conj (q t)).toMonoidHom =
      ((⊥ : Subgroup D).prod Q).map η := by
    rw [←h₁,Subgroup.map_inf _ _ _ (MulAut.conj (q t)).injective,hT,ht₁,h₂]
  have hE₂ : (((⊥ : Subgroup D).prod Q).map η).map (MulAut.conj (q t)).toMonoidHom =
      ((P : Subgroup D).prod ⊥).map η := by
    rw [←h₂,Subgroup.map_inf _ _ _ (MulAut.conj (q t)).injective,hT,ht₂,h₁]
  rcases haxis with haxis | haxis
  · have hA := elementary_subimage q (T : Subgroup G) B hB.1 _
      (show ((P : Subgroup D).prod ⊥).map η ≤ B.map q by rw [←hB₀map]; exact map_mono haxis)
    exact ⟨hA,conjugate_elementary_lift q (T : Subgroup G) _ _ t ht hE₁ hA⟩
  · have hA := elementary_subimage q (T : Subgroup G) B hB.1 _
      (show ((⊥ : Subgroup D).prod Q).map η ≤ B.map q by rw [←hB₀map]; exact map_mono haxis)
    exact ⟨conjugate_elementary_lift q (T : Subgroup G) _ _ t ht hE₂ hA,hA⟩

end CFSG.Quasithin.ChapterE.ThompsonAction.PairGeneration
