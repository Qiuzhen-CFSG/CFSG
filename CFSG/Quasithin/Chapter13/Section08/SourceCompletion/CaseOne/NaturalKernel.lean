module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalExchange
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.Cover
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.NaturalQuotient
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.SourceResidual

/-!
# Exact kernel and radical for the nonabelian natural branch

The constructed complement W₂ is fully moved by the literal point-pair
residual X₁. Symplectic duality makes U_H/V₃ irreducible for X₁, and
conjugation preserves that property for the chosen second seed span.
Its nontrivial star image therefore has kernel exactly V₃ˡ and order four.
The sign kernel is invariant and cannot have index four; hence the image
is even. It centralizes W₂, so its marked image is the even plane radical
D₀. The earlier edge marking identifies this with the actual O₂(L₁*).

All maps are the original star quotient and supplied whole-module natural
coordinates. The contrary full-denominator and nonabelian hypotheses are
retained here; this is an intermediate step of the source exclusion owned
by CaseOne, not the completed Lemma 13.8.33.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Lemma 13.8.33, printed p.966, final paragraph.
-/

public section
open Subgroup BinaryPermutation Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension
open A6Endgame.IntersectionBalance
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The natural seed quotient is chief for the literal point-pair residual;
conjugation preserves this statement for the chosen second seed span. -/
theorem natural_conjugate_seed_interval
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁) (hH : H = G₁)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6))
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      naturalRepresentation (Fin 6) (e g) (F v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.canonicalPlane)
    (l : L)
    (hW : V₁ ⊔ (V ⊓ Source.UH H V₃ ⊓ (Source.UH H V₃).conjBy (l : G)) = V₃)
    (hm : ⁅V ⊓ Source.UH H V₃ ⊓ (Source.UH H V₃).conjBy (l : G),
      residual (sourceOne L T V₁ ⊓ centralizer ((V₁ ⊔ V₁.conjBy (l : G) : Subgroup G) : Set G))⁆ =
        V ⊓ Source.UH H V₃ ⊓ (Source.UH H V₃).conjBy (l : G))
    (hX : (residual (sourceOne L T V₁ ⊓
      centralizer ((V₁ ⊔ V₁.conjBy (l : G) : Subgroup G) : Set G))).conjBy (l : G) =
        residual (sourceOne L T V₁ ⊓ centralizer ((V₁ ⊔ V₁.conjBy (l : G) : Subgroup G) : Set G)))
    (D : Subgroup G) (hPD : V₃.conjBy (l : G) ≤ D)
    (hDU : D ≤ (Source.UH H V₃).conjBy (l : G))
    (hn : residual (sourceOne L T V₁ ⊓
      centralizer ((V₁ ⊔ V₁.conjBy (l : G) : Subgroup G) : Set G)) ≤ normalizer (D : Set G)) :
    D = V₃.conjBy (l : G) ∨ D = (Source.UH H V₃).conjBy (l : G) := by
  let X := residual (sourceOne L T V₁ ⊓
    centralizer ((V₁ ⊔ V₁.conjBy (l : G) : Subgroup G) : Set G))
  let W := V ⊓ Source.UH H V₃ ⊓ (Source.UH H V₃).conjBy (l : G)
  have hXH : X ≤ H := by
    rw [hH, d.first_normalizer]
    exact (residual_le _).trans (inf_le_left.trans ((one_le _ _ _).trans inf_le_right))
  have hXi : X.conjBy (l : G)⁻¹ = X := by
    have he := congrArg (fun K : Subgroup G => K.conjBy (l : G)⁻¹) hX
    rw [conjBy_inv] at he
    exact he.symm
  have hPn : V₃ ≤ D.conjBy (l : G)⁻¹ := by
    have he := map_mono (f := (MulAut.conj (l : G)⁻¹).toMonoidHom) hPD
    change (V₃.conjBy (l : G)).conjBy (l : G)⁻¹ ≤ D.conjBy (l : G)⁻¹ at he
    rwa [conjBy_inv] at he
  have hUn : D.conjBy (l : G)⁻¹ ≤ Source.UH H V₃ := by
    have he := map_mono (f := (MulAut.conj (l : G)⁻¹).toMonoidHom) hDU
    change D.conjBy (l : G)⁻¹ ≤ ((Source.UH H V₃).conjBy (l : G)).conjBy (l : G)⁻¹ at he
    rwa [conjBy_inv] at he
  have hn' : X ≤ normalizer (D.conjBy (l : G)⁻¹ : Set G) := by
    rw [← hXi]
    exact (map_mono hn).trans (le_normalizer_map _)
  have hh := A6Endgame.ActionAnalysis33.natural_seed_interval a e F hF
    X W V₃ (D.conjBy (l : G)⁻¹) hXH (inf_le_left.trans inf_le_right)
    (le_conjugateSpanBy V₃ H) (d.line_le_plane.trans d.plane_le_seed)
    ((sup_comm _ _).trans hW) hm hp hPn hUn hn'
  rcases hh with hh | hh
  · left
    have he := congrArg (fun K : Subgroup G => K.conjBy (l : G)) hh
    rwa [conjBy_inv'] at he
  · right
    have he := congrArg (fun K : Subgroup G => K.conjBy (l : G)) hh
    rwa [conjBy_inv'] at he

omit [Finite G] in
private theorem star_even_of_seed_interval
    (B P X : Subgroup G) (hBH : B ≤ H) (hXH : X ≤ H)
    (hn : X ≤ normalizer (B : Set G))
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (hPB : P ≤ B) (hPQ : P ≤ Source.QH H)
    (hi : ∀ D : Subgroup G, P ≤ D → D ≤ B → X ≤ normalizer (D : Set G) →
      D = P ∨ D = B)
    (hidx : P.relIndex B = 4) :
    (Source.starImage H B).map e.toMonoidHom ≤ alternatingGroup (Fin 6) := by
  let s : H →* ℤˣ := Equiv.Perm.sign.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H)))
  let f : B →* ℤˣ := s.comp (inclusion hBH)
  let D := f.ker.map B.subtype
  have hPD : P ≤ D := by
    intro p hp
    let b : B := ⟨p, hPB hp⟩
    have hq : QuotientGroup.mk' (pCore 2 H) (inclusion hBH b) = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      obtain ⟨v, hv, he⟩ := hPQ hp
      have he' : v = inclusion hBH b := Subtype.ext he
      exact he' ▸ hv
    refine ⟨b, ?_, rfl⟩
    change Equiv.Perm.sign (e (QuotientGroup.mk' (pCore 2 H) (inclusion hBH b))) = 1
    rw [hq, map_one, map_one]
  have hXD : X ≤ normalizer (D : Set G) := by
    apply le_normalizer_iff.mpr
    rintro x hx y ⟨b, hb, rfl⟩
    have hm := (mem_normalizer_iff.mp (hn hx) b).mp b.property
    let c : B := ⟨x * (b : G) * x⁻¹, hm⟩
    refine ⟨c, ?_, rfl⟩
    have he : inclusion hBH c = (⟨x,hXH hx⟩ : H) * inclusion hBH b * ⟨x,hXH hx⟩⁻¹ :=
      Subtype.ext rfl
    change s (inclusion hBH c) = 1
    rw [he, map_mul, map_mul, map_inv, show s (inclusion hBH b) = 1 from hb,
      mul_one, mul_inv_cancel]
  have hD : D = B := by
    rcases hi D hPD (map_subtype_le _) hXD with he | he
    · have hk : D.subgroupOf B = f.ker := comap_map_eq_self_of_injective B.subtype_injective _
      have hcard : Nat.card f.range ≤ 2 := by
        have hb := Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
        simpa only [Nat.card_eq_fintype_card, Fintype.card_units_int] using hb
      have hh : D.relIndex B = Nat.card f.range := by
        change (D.subgroupOf B).index = _
        rw [hk, index_ker]
      rw [he, hidx] at hh
      omega
    · exact he
  rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  have hmem : (b : G) ∈ D := hD.symm ▸ hb
  obtain ⟨c, hc, he⟩ := hmem
  have he' : inclusion hBH c = b := Subtype.ext he
  have heq : s b = 1 := by
    rw [← he']
    exact hc
  exact heq

/-- In the actual nonabelian source branch, the chosen conjugate has its
exact seed as kernel in O₂(H), and its star image is the marked even radical. -/
theorem exists_nonabelian_marked_kernel
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    ∃ l : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left l)) ^ 2 = 1 ∧
      ¬ V₁.conjBy (l : G) ≤ V₃ ∧
      (Source.UH H V₃).conjBy (l : G) ≤ H ∧
      (Source.UH H V₃).conjBy (l : G) ⊓ Source.QH H = V₃.conjBy (l : G) ∧
      (Source.UH H V₃).conjBy (l : G) ⊓ V = V₃.conjBy (l : G) ∧
      Nat.card (Source.starImage H ((Source.UH H V₃).conjBy (l : G))) = 4 ∧
      (Source.starImage H ((Source.UH H V₃).conjBy (l : G))).map e.toMonoidHom =
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.D0 := by
  obtain ⟨F, hF, hp⟩ := natural_model_of_nonabelian d hF9 c hDH hDg hcentral a e model hn
  obtain ⟨l, hs, hout, hUH, hstar, hW⟩ :=
    exists_nonabelian_symmetric_movement d hF9 c hH hDH hDg hcentral hn
  dsimp only at hW
  rcases hW with ⟨_, hwjoin, _, _, _, _, _, hxUl, _, hmove, _, _, hxfix⟩
  let U := Source.UH H V₃
  let X := residual (sourceOne L T V₁ ⊓ centralizer ((V₁ ⊔ V₁.conjBy (l : G) : Subgroup G) : Set G))
  have hV : V.conjBy (l : G) = V :=
    mem_normalizer_iff_map_conj_eq.mp (d.normalizes_V (mem_sup_left l.property))
  have hPV : V₃.conjBy (l : G) ≤ V := (map_mono d.seed_le).trans hV.le
  have hVQ : V ≤ Source.QH H := (le_conjugateSpanBy V H).trans
    (Section07.VH_le_core (localNaturalSetup d) hF9
      (show IsMulCommutative (Source.UH H V₃) from inferInstance))
  have hXP : X ≤ H := by
    rw [hH, d.first_normalizer]
    exact (residual_le _).trans (inf_le_left.trans ((one_le _ _ _).trans inf_le_right))
  have hXn : X ≤ normalizer ((U.conjBy (l : G) ⊓ Source.QH H : Subgroup G) : Set G) :=
    (le_inf hxUl
      (hXP.trans (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH
        (D := Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H)))).trans inf_normalizer_le_normalizer_inf
  have hk : U.conjBy (l : G) ⊓ Source.QH H = V₃.conjBy (l : G) := by
    rcases natural_conjugate_seed_interval d hH a e F hF hp l hwjoin
      hmove hxfix
      (U.conjBy (l : G) ⊓ Source.QH H)
      (le_inf (map_mono (le_conjugateSpanBy V₃ H)) (hPV.trans hVQ)) inf_le_left hXn with he | he
    · exact he
    · exfalso
      apply hstar
      apply le_bot_iff.mp
      rintro _ ⟨u, hu, rfl⟩
      have hq : (u : G) ∈ Source.QH H := (he.symm.le hu).2
      obtain ⟨v, hv, he⟩ := hq
      have he' : v = u := Subtype.ext he
      exact (QuotientGroup.eq_one_iff u).mpr (he' ▸ hv)
  have hi : U.conjBy (l : G) ⊓ V = V₃.conjBy (l : G) := by
    have he := congrArg (fun K : Subgroup G => K.conjBy (l : G))
      (seed_intersection d hF9 c hDH hDg)
    change (V ⊓ U).map (MulAut.conj (l : G)).toMonoidHom = _ at he
    rw [map_inf _ _ _ (MulAut.conj (l : G)).injective] at he
    change V.conjBy (l : G) ⊓ U.conjBy (l : G) = _ at he
    rw [hV, inf_comm] at he
    exact he
  have hz : V₁ ≤ V₃ := d.line_le_plane.trans d.plane_le_seed
  have hc : V₁.relIndex U = 16 := by
    change Nat.card (Source.Utilde H V₃ V₁) = 16
    have he := Nat.card_congr F.toEquiv
    change Nat.card (Source.Utilde H V₃ V₁) = Nat.card (natural (Fin 6)) at he
    rw [he, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      finrank_natural_even (Fin 6) (by decide)]
    decide
  have hpidx : V₁.relIndex V₃ = 4 := by
    have he := (V₁.subgroupOf V₃).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hz).toEquiv, d.line_card, d.seed_card] at he
    change 2 * V₁.relIndex V₃ = 8 at he
    omega
  have hu : V₃.relIndex U = 4 := by
    have he := relIndex_mul_relIndex V₁ V₃ U hz (le_conjugateSpanBy V₃ H)
    rw [hc, hpidx] at he
    omega
  have hindex : (V₃.conjBy (l : G)).relIndex (U.conjBy (l : G)) = 4 := by
    exact (relIndex_map_map_of_injective V₃ U (MulAut.conj (l : G)).injective).trans hu
  have hcstar : Nat.card (Source.starImage H (U.conjBy (l : G))) = 4 := by
    rw [CriticalGeometry.starImage_card H _ hUH, ← inf_relIndex_left, hk]
    exact hindex
  have heven := star_even_of_seed_interval (U.conjBy (l : G))
    (V₃.conjBy (l : G)) X hUH hXP hxUl e
    (map_mono (le_conjugateSpanBy V₃ H)) (hPV.trans hVQ)
    (natural_conjugate_seed_interval d hH a e F hF hp l hwjoin hmove hxfix) hindex
  have hfix : (Source.starImage H (U.conjBy (l : G))).map e.toMonoidHom ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.D := by
    let : IsMulCommutative (U.conjBy (l : G)) := by
      let : IsElementaryAbelian 2 (U.conjBy (l : G)) := IsElementaryAbelian.map _
      infer_instance
    apply A6Endgame.ActionAnalysis33.natural_seed_fixer a e F hF
      (U.conjBy (l : G)) (V ⊓ U ⊓ U.conjBy (l : G)) V₃
      (inf_le_left.trans inf_le_right)
      ((d.line_le_plane.trans d.plane_le_seed).trans (le_conjugateSpanBy V₃ H))
      ((sup_comm _ _).trans hwjoin) hp
    exact (le_centralizer _).trans (centralizer_le inf_le_right)
  have hrad : (Source.starImage H (U.conjBy (l : G))).map e.toMonoidHom =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.D0 := by
    apply eq_of_le_of_card_ge (le_inf hfix heven)
    change Nat.card Theory.SpecificGroups.SymmetricSix.BinaryFlags.D0 ≤
      Nat.card ((Source.starImage H (U.conjBy (l : G))).map e.toMonoidHom)
    rw [card_map_of_injective e.injective, hcstar,
      Representation.SixLetterRadicalDisplacement.D0_card]
  exact ⟨l, hs, hout, hUH, hk, hi, hcstar, hrad⟩

/-- The actual earlier edge marking identifies the four-element star image
with O₂(L₁*) itself, preserving the original quotient and two-residual. -/
theorem exists_nonabelian_core_image
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hn : ¬ IsMulCommutative (Source.UL L H V₃))
    (hmark : (Source.starImage H ((L ⊔ (T : Subgroup G)) ⊓ H)).map e.toMonoidHom =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.H2) :
    ∃ l : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left l)) ^ 2 = 1 ∧
      ¬ V₁.conjBy (l : G) ≤ V₃ ∧
      (Source.UH H V₃).conjBy (l : G) ≤ H ∧
      (Source.UH H V₃).conjBy (l : G) ⊓ Source.QH H = V₃.conjBy (l : G) ∧
      (Source.UH H V₃).conjBy (l : G) ⊓ V = V₃.conjBy (l : G) ∧
      Nat.card (Source.starImage H ((Source.UH H V₃).conjBy (l : G))) = 4 ∧
      Source.starImage H ((Source.UH H V₃).conjBy (l : G)) =
        (Source.starImage H (sourceOne L T V₁)).pCoreIn 2 := by
  obtain ⟨l, hs, hout, hlH, hk, hi, hc, hrad⟩ :=
    exists_nonabelian_marked_kernel d hF9 c hH hDH hDg hcentral a e model hn
  have hres : sourceOne L T V₁ =
      (pResidual 2 ↥(H ⊓ (L ⊔ (T : Subgroup G)))).map (H ⊓ (L ⊔ (T : Subgroup G))).subtype := by
    change residual ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G)) =
      residual (H ⊓ (L ⊔ (T : Subgroup G)))
    rw [← d.first_normalizer, ← hH, inf_comm]
  have he := A6Endgame.SourceResidual.symmetric_core H (L ⊔ (T : Subgroup G))
    (sourceOne L T V₁) hres e (by rw [inf_comm H]; exact hmark)
  refine ⟨l, hs, hout, hlH, hk, hi, hc, ?_⟩
  exact Subgroup.map_injective e.injective (hrad.trans he.symm)

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
