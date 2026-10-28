module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.CartanPanel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MarkedLocal
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.CartanFixedPoints

/-!
# Original local Cartan complements on marked quotient panels

For an original F.1.1 pair and an independent finite marked quotient,
both endpoint maps carry the entire common Borel to the actual Borel B.
The local Borel is consequently the inverse image of B in its original
factor Lᵢ, and the original S ∩ Lᵢ is the inverse image of U. Normality
of Lᵢ in its own parabolic transports to that same marked factor image.

Pull H = B ∩ N back along the original factor map. The Borel intersection
factorization proves every supplied-complement premise for this actual
Cartan. The local Borel-coset equivalence retains the representative and
action formulas on the entire endpoint panel. The existing perfect PSL₂
and Suzuki fixed-pair theorems then prove simple-root containment in the
original factor image, using the finite commutator argument. No uniform
unitary fixed-pair result, whole-group equality or marked Lie recognition
is assumed or claimed. The final specializations retain the literal
quotient q of the actual generated source carrier; the general form also
applies to an independently marked finite universal quotient.

Source: Aschbacher--Smith F.1.1 and F.1.3, pp.259--260;
DGS, Groups and Graphs, Part II, pp.80--81 and Theorem D, p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)

@[expose] def factorInEndpoint (i : Fin 2) :
    L i →* Q.tits.standardParabolic {Q.simple i} :=
  (endpoint Q e i).toMonoidHom.comp
    (inclusion (show L i ≤ parabolic L S i from le_sup_left.trans le_sup_left))

private theorem endpointMap_inj (i : Fin 2) : Function.Injective (endpointMap Q e i) :=
  (Q.tits.standardParabolic {Q.simple i}).subtype_injective.comp (endpoint Q e i).injective

theorem factorMap_injective (i : Fin 2) : Function.Injective (factorMap Q e i) :=
  (endpointMap_inj Q e i).comp (inclusion_injective _)

theorem endpoint_borel_comap (h : HypothesisF11 L S) (i : Fin 2) :
    Q.tits.B.comap (endpointMap Q e i) = (commonBorel L S).subgroupOf (parabolic L S i) := by
  ext x
  constructor
  · intro hx
    let b : commonBorel L S ≃* Q.tits.B :=
      (MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm).trans e.middle
    obtain ⟨c, hc⟩ := b.surjective ⟨endpointMap Q e i x, hx⟩
    have hc' : borelMap Q e h c = endpointMap Q e i x := congrArg Subtype.val hc
    rw [← endpoint_borel Q e h i c] at hc'
    have he := endpointMap_inj Q e i hc'
    exact he ▸ c.property
  · intro hx
    have he := endpoint_borel Q e h i ⟨x,hx⟩
    change endpointMap Q e i x ∈ Q.tits.B
    rw [he]
    exact ((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm).trans e.middle
      ⟨x,hx⟩).property

theorem factor_borel_comap (h : HypothesisF11 L S) (i : Fin 2) :
    Q.tits.B.comap (factorMap Q e i) = (borel (L i) S).subgroupOf (L i) := by
  ext x
  change endpointMap Q e i _ ∈ Q.tits.B ↔ (x : G) ∈ borel (L i) S
  rw [← h.local_inf_commonBorel i]
  change _ ↔ (x : G) ∈ L i ∧ (x : G) ∈ commonBorel L S
  rw [← mem_comap, endpoint_borel_comap Q e h i]
  exact ⟨fun hx => ⟨x.property,hx⟩, fun hx => hx.2⟩

theorem factor_unipotent_comap (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) :
    split.U.comap (factorMap Q e i) = (S ⊓ L i).subgroupOf (L i) := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := (sylow_range Q e h split).symm ▸ hx
    rw [← endpoint_sylow Q e h i s] at hs
    have he := congrArg Subtype.val (endpointMap_inj Q e i hs)
    refine ⟨?_, x.property⟩
    change (x : G) ∈ S
    change (s : G) = (x : G) at he
    rw [← he]
    exact s.property
  · intro hx
    rw [← sylow_range Q e h split]
    refine ⟨⟨x,hx.1⟩, ?_⟩
    exact (endpoint_sylow Q e h i ⟨x,hx.1⟩).symm

theorem factor_parabolic_normalizes (h : HypothesisF11 L S) (i : Fin 2) :
    Q.tits.standardParabolic {Q.simple i} ≤ normalizer ((factorMap Q e i).range : Set (X ⧸ Q.D)) := by
  let := h.local_normal_in_parabolic i
  intro y hy
  obtain ⟨x, hx⟩ := (endpoint Q e i).surjective ⟨y,hy⟩
  have hxnorm : x ∈ normalizer ((L i).subgroupOf (parabolic L S i) :
      Set (parabolic L S i)) := by
    rw [normalizer_eq_top_iff.mpr (h.local_normal_in_parabolic i)]
    exact mem_top _
  have hn := (le_normalizer_map (endpointMap Q e i))
    (mem_map_of_mem (endpointMap Q e i) hxnorm)
  have hn' : endpointMap Q e i x ∈
      normalizer ((factorMap Q e i).range : Set (X ⧸ Q.D)) := by
    simpa only [factorMap, MonoidHom.range_comp, inclusion_range] using hn
  have hx' : endpointMap Q e i x = y := congrArg Subtype.val hx
  rwa [hx'] at hn'

theorem factorInEndpoint_normal (h : HypothesisF11 L S) (i : Fin 2) :
    (factorInEndpoint Q e i).range.Normal := by
  rw [factorInEndpoint, MonoidHom.range_comp, inclusion_range]
  exact (h.local_normal_in_parabolic i).map
    (endpoint Q e i).toMonoidHom (endpoint Q e i).surjective

theorem factorInEndpoint_generates_panel (h : HypothesisF11 L S) (i : Fin 2) :
    (factorInEndpoint Q e i).range ⊔
      Q.tits.B.subgroupOf (Q.tits.standardParabolic {Q.simple i}) = ⊤ := by
  have hC : (Q.tits.B.subgroupOf (Q.tits.standardParabolic {Q.simple i})).comap
      (endpoint Q e i).toMonoidHom =
      (commonBorel L S).subgroupOf (parabolic L S i) :=
    endpoint_borel_comap Q e h i
  have hC' := congrArg (Subgroup.map (endpoint Q e i).toMonoidHom) hC
  rw [map_comap_eq, MonoidHom.range_eq_top.mpr (endpoint Q e i).surjective,
    top_inf_eq] at hC'
  rw [hC', factorInEndpoint, MonoidHom.range_comp, inclusion_range, ← Subgroup.map_sup,
    ← subgroupOf_sup (show L i ≤ parabolic L S i from le_sup_left.trans le_sup_left)
      (commonBorel_le_parabolic i), ← parabolic_eq_sup_commonBorel, subgroupOf_self,
    map_top_of_surjective _ (endpoint Q e i).surjective]

/-- Pull back the actual H along the original factor marking. -/
@[expose] def localCartan (i : Fin 2) : Subgroup (L i) :=
  (Q.tits.B ⊓ Q.tits.N).comap (factorMap Q e i)

theorem localCartan_image (i : Fin 2) :
    (localCartan Q e i).map (factorMap Q e i) =
      (factorMap Q e i).range ⊓ (Q.tits.B ⊓ Q.tits.N) := map_comap_eq _ _

/-- The supplied complement is the literal original-factor intersection with H. -/
theorem localCartan_complement (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) :
    localCartan Q e i ≤ (borel (L i) S).subgroupOf (L i) ∧
      Nat.Coprime 2 (Nat.card (localCartan Q e i)) ∧
      Disjoint ((S ⊓ L i).subgroupOf (L i)) (localCartan Q e i) ∧
      (S ⊓ L i).subgroupOf (L i) ⊔ localCartan Q e i =
        (borel (L i) S).subgroupOf (L i) := by
  have hD : localCartan Q e i ≤ (borel (L i) S).subgroupOf (L i) := by
    rw [← factor_borel_comap Q e h i]
    exact comap_mono inf_le_left
  refine ⟨hD, ?_, ?_, ?_⟩
  · rw [Nat.card_congr ((localCartan Q e i).equivMapOfInjective
      (factorMap Q e i) (factorMap_injective Q e i)).toEquiv, localCartan_image]
    exact split.odd.of_dvd_right (card_dvd_of_le inf_le_right)
  · apply disjoint_def.mpr
    intro x hx hdx
    apply (factorMap_injective Q e i)
    rw [map_one]
    apply mem_bot.mp
    rw [← split.unipotent_inf_N]
    refine ⟨?_, hdx.2⟩
    change x ∈ split.U.comap (factorMap Q e i)
    rw [factor_unipotent_comap Q e h split i]
    exact hx
  · apply (map_injective (factorMap_injective Q e i))
    rw [← factor_unipotent_comap Q e h split i, ← factor_borel_comap Q e h i,
      Subgroup.map_sup, map_comap_eq, localCartan_image, map_comap_eq]
    exact normal_borel_intersection_factorization split _
      ((Q.tits.B_le_standardParabolic _).trans (factor_parabolic_normalizes Q e h i))

open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.CartanPanel

/-- The source local Borel cosets identify with the entire endpoint panel,
using the original factor inclusion followed by its marked endpoint map. -/
def localBorelPanel (h : HypothesisF11 L S) (i : Fin 2) :
    (L i) ⧸ (borel (L i) S).subgroupOf (L i) ≃ Panel Q i :=
  supplementCosetEquiv (factorInEndpoint Q e i) _ _ (factor_borel_comap Q e h i)
    (factorInEndpoint_normal Q e h i) (factorInEndpoint_generates_panel Q e h i)

@[simp] theorem localBorelPanel_mk (h : HypothesisF11 L S) (i : Fin 2) (x : L i) :
    localBorelPanel Q e h i (QuotientGroup.mk x) =
      QuotientGroup.mk (factorInEndpoint Q e i x) := by
  exact supplementCosetEquiv_mk _ _ _ _ _ _ x

theorem localBorelPanel_smul (h : HypothesisF11 L S) (i : Fin 2)
    (x : L i) (ω : (L i) ⧸ (borel (L i) S).subgroupOf (L i)) :
    localBorelPanel Q e h i (x • ω) =
      factorInEndpoint Q e i x • localBorelPanel Q e h i ω :=
  supplementCosetEquiv_smul _ _ _ _ _ _ x ω

/-- Local fixed pairs transfer to the literal standard-parabolic panel. -/
theorem localCartan_two_fixed_on_panel (h : HypothesisF11 L S) (i : Fin 2)
    (hfix : HasTwoFixedCosets ((borel (L i) S).subgroupOf (L i)) (localCartan Q e i)) :
    HasTwoFixedCosets
      (Q.tits.B.subgroupOf (Q.tits.standardParabolic {Q.simple i}))
      (((factorMap Q e i).range ⊓ (Q.tits.B ⊓ Q.tits.N)).subgroupOf
        (Q.tits.standardParabolic {Q.simple i})) := by
  have him : (localCartan Q e i).map (factorInEndpoint Q e i) =
      (((factorMap Q e i).range ⊓ (Q.tits.B ⊓ Q.tits.N)).subgroupOf
        (Q.tits.standardParabolic {Q.simple i})) := by
    apply (map_injective (Q.tits.standardParabolic {Q.simple i}).subtype_injective)
    rw [map_map, map_subgroupOf_eq_of_le]
    · exact localCartan_image Q e i
    · exact inf_le_left.trans (by
        rintro _ ⟨x,rfl⟩
        exact (factorInEndpoint Q e i x).property)
  rw [← him]
  exact two_fixed_pushforward_of_normal_range (factorInEndpoint Q e i) _ _
    (show (Q.tits.B.subgroupOf (Q.tits.standardParabolic {Q.simple i})).comap
      (factorInEndpoint Q e i) = (borel (L i) S).subgroupOf (L i) from
        factor_borel_comap Q e h i)
    (factorInEndpoint_normal Q e h i) (factorInEndpoint_generates_panel Q e h i) _ hfix

/-- Discharge the fixed-point-free and commutator premises on the same source factor. -/
theorem simpleRoot_le_factor_of_localCartan (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2)
    (hfix : HasTwoFixedCosets ((borel (L i) S).subgroupOf (L i)) (localCartan Q e i)) :
    simpleRoot Q split i ≤ (factorMap Q e i).range :=
  simpleRoot_le_of_two_fixed_cosets Q split i _ (factor_parabolic_normalizes Q e h i)
    (localCartan_two_fixed_on_panel Q e h i hfix)

/-- The perfect linear source branch supplies the actual Cartan fixed-pair
input, rather than a new root-centralizer assumption. -/
theorem simpleRoot_le_factor_linear (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (hp : Group.IsPerfect (L i)) (n : ℕ) (hn : 0 < n)
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2 ^ n)) :
    simpleRoot Q split i ≤ (factorMap Q e i).range := by
  obtain ⟨hD,hodd,hdis,hsup⟩ := localCartan_complement Q e h split i
  exact simpleRoot_le_factor_of_localCartan Q e h split i
    (h.borel_two_fixed_cosets_linear i hp n hn hmodel _ hD hodd hdis hsup)

/-- The perfect Suzuki source branch uses its original quotient isomorphism
and the same marked factor and actual Cartan complement. -/
theorem simpleRoot_le_factor_suzuki (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (hp : Group.IsPerfect (L i)) (m : ℕ)
    (emodel : ((L i) ⧸ pCore 2 (L i)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    simpleRoot Q split i ≤ (factorMap Q e i).range := by
  obtain ⟨hD,hodd,hdis,hsup⟩ := localCartan_complement Q e h split i
  exact simpleRoot_le_factor_of_localCartan Q e h split i
    (h.borel_two_fixed_cosets_suzuki i hp m emodel _ hD hodd hdis hsup)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The independent-carrier factor map specializes to the same original quotient map. -/
theorem original_factorMap_apply (Q : SourceQuotient L S) (i : Fin 2) (x : L i) :
    MarkedLocal.factorMap Q (originalMarkedIso Q) i x =
      Q.q ⟨x, local_le_generated i x.property⟩ := by
  fin_cases i
  · exact originalMarkedIso_left_apply Q _
  · exact originalMarkedIso_right_apply Q _

theorem original_factorMap_range (Q : SourceQuotient L S) (i : Fin 2) :
    (MarkedLocal.factorMap Q (originalMarkedIso Q) i).range =
      ((L i).subgroupOf (generated L S)).map Q.q := by
  have hf : MarkedLocal.factorMap Q (originalMarkedIso Q) i =
      Q.q.comp (inclusion (local_le_generated i)) :=
    MonoidHom.ext (original_factorMap_apply Q i)
  rw [hf, MonoidHom.range_comp, inclusion_range]

/-- The actual original quotient's linear simple root lies in the image of
its corresponding original local factor, with neither endpoint marking changed. -/
theorem quotient_simpleRoot_le_original_factor_linear (h : HypothesisF11 L S)
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (i : Fin 2)
    (hp : Group.IsPerfect (L i)) (n : ℕ) (hn : 0 < n)
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2 ^ n)) :
    simpleRoot Q split i ≤ ((L i).subgroupOf (generated L S)).map Q.q := by
  rw [← original_factorMap_range Q i]
  exact MarkedLocal.simpleRoot_le_factor_linear Q (originalMarkedIso Q) h split i hp n hn hmodel

/-- The same original-quotient conclusion for the perfect Suzuki branch. -/
theorem quotient_simpleRoot_le_original_factor_suzuki (h : HypothesisF11 L S)
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (i : Fin 2)
    (hp : Group.IsPerfect (L i)) (m : ℕ)
    (emodel : ((L i) ⧸ pCore 2 (L i)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    simpleRoot Q split i ≤ ((L i).subgroupOf (generated L S)).map Q.q := by
  rw [← original_factorMap_range Q i]
  exact MarkedLocal.simpleRoot_le_factor_suzuki Q (originalMarkedIso Q) h split i hp m emodel

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

