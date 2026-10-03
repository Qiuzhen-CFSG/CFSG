module
public import Stellmacher.SectionOne.OneSevenFactorOrbitTransitivity
public import Stellmacher.SectionOne.LemmaOneSeven
public import Mathlib.GroupTheory.RegularWreathProduct
public import Stellmacher.TwoSL2FactorsWreathRecognition
public import Mathlib.GroupTheory.NoncommCoprod


/-!
# Wreath recognition for two canonical one-seven factors

Under the Section One hypotheses, suppose the one-seven product generates
the group with its Sylow two-subgroup, the Sylow has a unique maximal
overgroup, and the canonical one-seven family has two members. Then the
ambient group is isomorphic to the literal `SL₂(2) ≀ᵣ C₂` model.

The canonical factors are commuting, disjoint copies of `SL₂(2)` and their
join is normal. Conjugation preserves their pair, and Sylow transitivity
provides a swapping element. Their common centralizer is trivial: each
factor is center-free, so the centralizer meets their join trivially. It
therefore embeds in the quotient by that join, which is a two-group by
Sylow generation. The centralizer is consequently a normal two-subgroup
and vanishes by the Section One two-core hypothesis. The generic
factor-permuting extension theorem now constructs the concrete wreath
isomorphism, correcting the swapping element to an involution internally.

This is the group-recognition part of the application of Stellmacher (1.7)
in (9.3), Journal of Algebra 190 (1997), p.50, and the corresponding
two-factor conclusion in (9.1). The supplied action determines the actual
canonical family; no Sylow-order assumption is added. Triviality of the
one-seven fixed complement is not needed for this group-only conclusion.
-/

namespace Stellmacher.SectionOne
open Subgroup
universe u

private theorem centralizer_join_eq_bot
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (D F : Subgroup G) (hD : IsSL2Two D) (hF : IsSL2Two F)
    (hcomm : D ≤ centralizer (F : Set G)) [(D ⊔ F).Normal]
    (hgen : (D ⊔ F) ⊔ (S : Subgroup G) = ⊤) :
    centralizer ((D ⊔ F : Subgroup G) : Set G) = ⊥ := by
  let E := D ⊔ F
  let C := centralizer (E : Set G)
  have hcross (d : D) (f : F) : Commute (d : G) (f : G) :=
    ((mem_centralizer_iff.mp (hcomm d.property)) f f.property).symm
  let prod : D × F →* G := D.subtype.noncommCoprod F.subtype hcross
  have hrange : prod.range = E := by
    exact (MonoidHom.noncommCoprod_range D.subtype F.subtype hcross).trans
      (congrArg₂ (· ⊔ ·) D.range_subtype F.range_subtype)
  have hinter : C ⊓ E = ⊥ := by
    apply le_bot_iff.mp
    rintro x ⟨hc, he⟩
    rw [← hrange] at he
    obtain ⟨⟨d, f⟩, rfl⟩ := he
    change (d : G) * (f : G) ∈ C at hc
    have hdcenter : d ∈ center D := by
      rw [mem_center_iff]
      intro a
      apply Subtype.ext
      have he := mem_centralizer_iff.mp hc (a : G) (show (a : G) ∈ E from mem_sup_left a.property)
      have hfa := (hcross a f).eq
      change (a : G) * (d : G) = (d : G) * (a : G)
      apply mul_right_cancel (b := (f : G))
      calc
        ((a : G) * (d : G)) * (f : G) = (a : G) * ((d : G) * (f : G)) := mul_assoc _ _ _
        _ = ((d : G) * (f : G)) * (a : G) := he
        _ = ((d : G) * (a : G)) * (f : G) := by rw [mul_assoc, ← hfa, ← mul_assoc]
    have hd1 : d = 1 := by
      rwa [RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two hD] at hdcenter
    subst d
    simp only [coe_one, one_mul] at hc ⊢
    have hfcenter : f ∈ center F := by
      rw [mem_center_iff]
      intro a
      exact Subtype.ext (mem_centralizer_iff.mp hc a (mem_sup_right a.property))
    have hf1 : f = 1 := by
      rwa [RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two hF] at hfcenter
    rw [hf1]
    exact (map_one prod) ▸ (one_mem _ : (1 : G) ∈ (⊥ : Subgroup G))
  let π := QuotientGroup.mk' E
  have hQtwo : IsPGroup 2 (G ⧸ E) := by
    have hSmap : (S : Subgroup G).map π = ⊤ := by
      have hh := congrArg (fun K : Subgroup G => K.map π) hgen
      rw [Subgroup.map_sup, show (D ⊔ F).map π = ⊥ from QuotientGroup.map_mk'_self E,
        bot_sup_eq, map_top_of_surjective π (QuotientGroup.mk'_surjective E)] at hh
      exact hh
    have hh := S.isPGroup'.map π
    rw [hSmap] at hh
    exact hh.of_equiv topEquiv
  have hCinj : Function.Injective (π.comp C.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_bot_iff.mp
    intro c hc
    have hπ : π (c : G) = 1 := hc
    have hE : (c : G) ∈ E := (QuotientGroup.eq_one_iff _).mp hπ
    apply Subtype.ext
    exact mem_bot.mp (hinter ▸ (show (c : G) ∈ C ⊓ E from ⟨c.property, hE⟩))
  have hCtwo : IsPGroup 2 C := hQtwo.of_injective (π.comp C.subtype) hCinj
  have hCle : C ≤ pCore 2 G := le_sSup ⟨inferInstance, hCtwo⟩
  exact le_bot_iff.mp (hCle.trans_eq h.twoCore_eq_bot)

private theorem canonical_pair_data
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hgen : oneE (V := V) (S : Subgroup G) ⊔ (S : Subgroup G) = ⊤)
    (hunique : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G))
    (htwo : (oneSevenFactors (G := G) (V := V)).card = 2) :
    ∃ D F : Subgroup G, IsSL2Two D ∧ IsSL2Two F ∧
      D ≤ centralizer (F : Set G) ∧ Disjoint D F ∧ (D ⊔ F).Normal ∧
      centralizer ((D ⊔ F : Subgroup G) : Set G) = ⊥ ∧
      (∀ g : G, (D.conjBy g = D ∧ F.conjBy g = F) ∨
        (D.conjBy g = F ∧ F.conjBy g = D)) ∧
      ∃ x : G, D.conjBy x = F := by
  classical
  let factors := oneSevenFactors (G := G) (V := V)
  obtain ⟨D, F, hDF, hpair⟩ := Finset.card_eq_two.mp htwo
  have hDmem : D ∈ factors := by simp [factors, hpair]
  have hFmem : F ∈ factors := by simp [factors, hpair]
  have hD := (mem_oneSevenFactors_iff D).mp hDmem
  have hF := (mem_oneSevenFactors_iff F).mp hFmem
  obtain ⟨hEn, hprod, _⟩ := oneSeven_global_product h S
  have hEpair : oneSevenGenerated (G := G) (V := V) = D ⊔ F := by
    rw [hprod.1]
    apply le_antisymm
    · apply iSup_le
      intro K
      have hK := K.property
      have hKpair : K.val ∈ ({D,F} : Finset (Subgroup G)) := hpair ▸ hK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hKpair
      rcases hKpair with he | he <;> rw [he]
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup (fun K : {K : Subgroup G // K ∈ factors} => K.val) ⟨D, hDmem⟩)
        (le_iSup (fun K : {K : Subgroup G // K ∈ factors} => K.val) ⟨F, hFmem⟩)
  have hcomm : D ≤ centralizer (F : Set G) := by
    intro d hd f hf
    exact (hprod.2.2.2 D hDmem F hFmem hDF d hd f hf).symm
  have hnormal : (D ⊔ F).Normal := hEpair ▸ hEn
  let _ := hnormal
  have hpairgen : (D ⊔ F) ⊔ (S : Subgroup G) = ⊤ := by
    rw [← hEpair, ← (oneSeven_global_identification h S).2]
    exact hgen
  have hcent := centralizer_join_eq_bot h S D F hD.1 hF.1 hcomm hpairgen
  have hposs (K : Subgroup G) (hK : K ∈ factors) (g : G) : K.conjBy g = D ∨ K.conjBy g = F := by
    have hh := (mem_oneSevenFactors_iff _).mpr ( ((mem_oneSevenFactors_iff K).mp hK).conjBy K g)
    rw [hpair] at hh
    simpa using hh
  have hperm (g : G) : (D.conjBy g = D ∧ F.conjBy g = F) ∨
      (D.conjBy g = F ∧ F.conjBy g = D) := by
    have hne : D.conjBy g ≠ F.conjBy g :=
      fun he => hDF (Subgroup.map_injective (MulAut.conj g).injective he)
    rcases hposs D hDmem g with hd | hd <;> rcases hposs F hFmem g with hf | hf
    · exact (hne (hd.trans hf.symm)).elim
    · exact Or.inl ⟨hd,hf⟩
    · exact Or.inr ⟨hd,hf⟩
    · exact (hne (hd.trans hf.symm)).elim
  obtain ⟨x,hx⟩ := oneSeven_factor_orbit_transitive h S hgen hunique D hDmem F hFmem
  exact ⟨D,F,hD.1,hF.1,hcomm,hprod.2.2.1 D hDmem F hFmem hDF,hnormal,hcent,hperm,⟨x,hx⟩⟩

/-- Two canonical factors with the local Sylow generation and maximality
hypotheses give the concrete SL₂(2) wreath-product group. -/
public theorem oneSeven_wreath_of_two_factors
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hgen : oneE (V := V) (S : Subgroup G) ⊔ (S : Subgroup G) = ⊤)
    (hunique : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G))
    (htwo : (oneSevenFactors (G := G) (V := V)).card = 2) :
    Nonempty (G ≃* RegularWreathProduct
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))) := by
  obtain ⟨D,F,hD,hF,hcomm,hdis,hnormal,hcent,hperm,hswap⟩ :=
    canonical_pair_data h S hgen hunique htwo
  let _ := hnormal
  exact Stellmacher.wreath_of_two_sl2_factors D F hD hF hcomm hdis hcent hperm hswap

end Stellmacher.SectionOne
