module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.FixedLine
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TrivialCenter
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Center identities along epsilon-two edges

Triviality of the enlarged local center removes the natural section's central
kernel. Its Sylow fixed line is the omega-center of the literal edge two-core.
Every subgroup of that Sylow escaping the vertex core has precisely this
commutator. At a critical edge this proves R = Z_beta. The earlier adjacent-core
obstruction applies the same calculation to Q_beta; local transitivity then
proves [V_beta,Q_beta] = Z_beta, including the center vertex in V_beta.

The natural-center predicate carries an actual surjective matrix actor with
kernel Q and an equivariant section with kernel Omega_1(Z(L)). It is constructed
from the recognized quotient isomorphism, rather than from a family tag.
`EpsilonTwoCenters` supplies both path ends and the reduced-source application.

Source: DGS, *Groups and Graphs* (1985), (7.4)(c--d), p.128. The exact preceding
local model and (6.5) obstruction remain explicit inputs.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u
variable {G : Type u} [Group G]

/-- Literal natural coordinates, including the actor's exact two-core kernel. -/
@[expose] def HasNaturalCenter (L Z Q : Subgroup G) : Prop :=
  ∃ (k : Type u) (_ : Field k) (_ : Finite k) (_ : Algebra (ZMod 2) k),
    ∃ π : L →* SL(2,k), Function.Surjective π ∧ π.ker = Q.subgroupOf L ∧
      Nonempty (BinaryConjugationSection L Z (Stellmacher.omegaOneCenterAmbient L)
        (SL2NaturalOffenders.NoStrong.natural.comp π))

/-- Recognition supplies the same natural coordinates without changing either kernel. -/
theorem hasNaturalCenter_of_marked
    (L Z Q : Subgroup G) [(Q.subgroupOf L).Normal]
    {k : Type u} [Field k] [Finite k] [Algebra (ZMod 2) k]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (L ⧸ Q.subgroupOf L) W)
    (d : BinaryConjugationSection L Z (Stellmacher.omegaOneCenterAmbient L)
      (σ.comp (QuotientGroup.mk' (Q.subgroupOf L))))
    (e : (L ⧸ Q.subgroupOf L) ≃* SL(2,k)) (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (hE : ∀ a w, E (σ a w) = Matrix.mulVec (e a).val (E w)) :
    HasNaturalCenter L Z Q := by
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (Q.subgroupOf L))
  refine ⟨k,inferInstance,inferInstance,inferInstance,π,
    e.surjective.comp (QuotientGroup.mk'_surjective _),?_,?_⟩
  · ext a
    change e (QuotientGroup.mk' (Q.subgroupOf L) a) = 1 ↔ _
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff a
  · exact ⟨{
      section_le := d.section_le
      kernel_le := d.kernel_le
      normalized := d.normalized
      coordinates := E.toAddEquiv.toMultiplicative.toMonoidHom.comp d.coordinates
      onto := E.toAddEquiv.toMultiplicative.surjective.comp d.onto
      kernel_eq := by
        ext z
        change E (d.coordinates z).toAdd = 0 ↔ (z:G) ∈ Stellmacher.omegaOneCenterAmbient L
        rw [E.map_eq_zero_iff]
        exact d.coordinates_eq_one_iff z
      equivariant a z := by
        change E (d.coordinates _).toAdd = Matrix.mulVec (π a).val (E (d.coordinates z).toAdd)
        rw [d.equivariant]
        exact hE _ _ }⟩

/-- In an elementary subgroup containing the Sylow seed, its Sylow fixed group is that seed. -/
theorem elementary_fixed_eq_seed (Z S : Subgroup G) [IsElementaryAbelian 2 Z]
    (hZS : Z ≤ S) (hseed : Stellmacher.omegaOneCenterAmbient S ≤ Z) :
    Z ⊓ centralizer (S : Set G) = Stellmacher.omegaOneCenterAmbient S := by
  apply le_antisymm
  · intro z hz
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff S z).mpr
      ⟨hZS hz.1,elemPow_eq_one_of_isElementaryAbelian z hz.1,hz.2⟩
  · intro z hz
    exact ⟨hseed hz,(Stellmacher.mem_omegaOneCenterAmbient_iff S z).mp hz |>.2.2⟩

/-- The graph's literal natural center has the required edge commutator for every
subgroup of the edge Sylow escaping the vertex core. -/
theorem graph_natural_edge_commutator
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v u : Vertex (family P)} (he : (graph (family P)).Adj v u)
    (c : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) u))
    (ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer (family P) v))
    (hcenter : center c.Pstar = ⊥)
    (hnat : HasNaturalCenter c.Pstar (Z (family P) v) (Q (family P) v))
    (A : Subgroup G)
    (hAS : A ≤ (stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2)
    (hAQ : ¬ A ≤ Q (family P) v) :
    ⁅Z (family P) v,A⁆ = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2) := by
  let := finite_endpoints h
  let : Finite c.Pstar := Finite.of_injective (inclusion c.Pstar_le) (inclusion_injective _)
  let := graph_Z_elementary h v
  let S := (stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2
  have hS := local_sylow_eq_edgeCore c ho (source_edge_core_sylow h hB he)
  have hSL : S ≤ c.Pstar := by
    change (stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2 ≤ c.Pstar
    rw [←hS]
    exact map_subtype_le _
  have hAL := hAS.trans hSL
  obtain ⟨k,hk,hfin,halg,π,hπ,hker,⟨d⟩⟩ := hnat
  have hω : Stellmacher.omegaOneCenterAmbient c.Pstar = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    obtain ⟨hxL,hxs,hxc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx
    have hxZ : (⟨x,hxL⟩ : c.Pstar) ∈ center c.Pstar := by
      apply mem_center_iff.mpr
      intro l
      exact Subtype.ext (hxc l l.property)
    rw [hcenter,mem_bot] at hxZ
    exact congrArg Subtype.val hxZ
  let d₀ : BinaryConjugationSection c.Pstar (Z (family P) v) ⊥
      (SL2NaturalOffenders.NoStrong.natural.comp π) := hω ▸ d
  let T := c.sylow.mapSurjective (f := π) hπ
  have hT : (S.subgroupOf c.Pstar).map π = T := by
    have hh : S.subgroupOf c.Pstar = c.sylow := by
      apply map_injective c.Pstar.subtype_injective
      rw [map_subgroupOf_eq_of_le hSL]
      exact hS.symm
    rw [hh]
    rfl
  have hne : (A.subgroupOf c.Pstar).map π ≠ ⊥ := by
    intro hh
    have hl := (Subgroup.map_eq_bot_iff _).mp hh
    rw [hker] at hl
    exact hAQ (fun a ha => hl (show (⟨a,hAL ha⟩ : c.Pstar) ∈ A.subgroupOf c.Pstar from ha))
  rw [natural_section_commutator c.Pstar (Z (family P) v) π d₀ A S hAL hSL T hT hAS hne]
  apply elementary_fixed_eq_seed
  · exact ((source_Z_Q_U h v).1.trans (map_subtype_le _)).trans (graph_Q_le_edgeCore h he)
  · exact graph_edgeSeed_le_Z h hB he c ho

/-- Local transitivity extends the one-edge commutator to the full radius-one span.
The center vertex is included and its contribution is proved trivial. -/
theorem graph_radius_one_commutator_of_edge
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    {v u : Vertex (family P)} (he : (graph (family P)).Adj v u)
    (hcomm : ⁅Z (family P) v,Q (family P) u⁆ = Z (family P) u) :
    ⁅V (family P) u 1,Q (family P) u⁆ = Z (family P) u := by
  let := finite_endpoints h
  have hnZ : stabilizer (family P) u ≤ normalizer (Z (family P) u : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ _)).mp (Z_normal _ _)
  have hneighbor (x : Vertex (family P)) (hx : (graph (family P)).Adj u x) :
      ⁅Z (family P) x,Q (family P) u⁆ = Z (family P) u := by
    obtain ⟨g,hg,hgx⟩ := locally_transitive (family P) he.symm hx
    have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hcomm
    rw [map_commutator,←Z_translate,←Q_translate,←Z_translate,hgx,
      show g • u = u from hg] at hh
    exact hh
  have hV : V (family P) u 1 = ⨆ x : ball (family P) u 1, Z (family P) x.val := by
    simp only [V,iSup_subtype]
  apply le_antisymm
  · rw [hV]
    apply commutator_iSup_le_of_relative_normal (stabilizer (family P) u)
      (Q (family P) u) (Z (family P) u) _ hnZ
    · intro x
      rcases (mem_ball_one (family P) u x.val).mp x.property with hx | hx
      · exact ((source_Z_Q_U h x.val).1.trans (map_subtype_le _)).trans
          ((source_Z_Q_U h x.val).2.trans
            ((ballKernel_one_le_edge (family P) hx.symm).trans inf_le_right))
      · rw [←hx]
        exact Z_le_stabilizer _ _
    · intro x
      rcases (mem_ball_one (family P) u x.val).mp x.property with hx | hx
      · exact (hneighbor x.val hx).le
      · rw [←hx,commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr (graph_Q_centralizes_Z h u)]
        exact bot_le
  · rw [←hcomm]
    exact commutator_mono
      (le_iSup_of_le v (le_iSup_of_le ((mem_ball_one _ _ _).mpr (Or.inl he.symm)) le_rfl)) le_rfl

/-- DGS (7.4)(c--d) at the first edge of the critical path. The local-center
and edge-normality calculations are discharged from the exact earlier premises. -/
theorem graph_epsilonTwo_forward_identities
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    {v w u : Vertex (family P)} (_hc : IsCriticalPair (family P) v w)
    (he : (graph (family P)).Adj v u)
    (hd : (graph (family P)).dist u w + 1 = b (family P))
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (c₀ : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) u))
    (c₁ : LocalRankOneData (stabilizer (family P) u)
      (stabilizer (family P) u ⊓ stabilizer (family P) v))
    (ho₀ : ¬ 2 ∣ c₀.Pstar.relIndex (stabilizer (family P) v))
    (ho₁ : ¬ 2 ∣ c₁.Pstar.relIndex (stabilizer (family P) u))
    (hdich : Stellmacher.IsSylowSubgroupIn (Q (family P) u)
      (c₁.Pstar ⊓ centralizer (Z (family P) u : Set G)) ∨
      Z (family P) u = Stellmacher.omegaOneCenterAmbient c₁.Pstar)
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat : HasNaturalCenter c₀.Pstar (Z (family P) v) (Q (family P) v))
    (hob : ¬ stabilizer (family P) u ≤ normalizer
      ((Q (family P) v ⊓ Q (family P) u : Subgroup G) : Set G)) :
    ⁅Z (family P) v,Z (family P) w⁆ = Z (family P) u ∧
      ⁅V (family P) u 1,Q (family P) u⁆ = Z (family P) u := by
  have hcenter := graph_epsilonTwo_center_trivial_of_localData h hB he c₀ c₁
    ho₀ ho₁ hdich hepsilon
  have hQS : Q (family P) u ≤
      (stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2 := by
    simpa only [inf_comm] using graph_Q_le_edgeCore h he.symm
  have hZQ : Z (family P) w ≤ Q (family P) u := by
    apply graph_Z_le_Q_of_short h hS
    rw [SimpleGraph.dist_comm]
    omega
  have hZesc : ¬ Z (family P) w ≤ Q (family P) v := by
    intro hh
    apply hne
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
    exact hh.trans (graph_Q_centralizes_Z h v)
  have hQesc : ¬ Q (family P) u ≤ Q (family P) v := by
    intro hh
    apply hob
    rw [inf_eq_right.mpr hh]
    exact (stabilizer (family P) u).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hR := graph_natural_edge_commutator h hB he c₀ ho₀ hcenter hnat
    (Z (family P) w) (hZQ.trans hQS) hZesc
  have hQ := graph_natural_edge_commutator h hB he c₀ ho₀ hcenter hnat
    (Q (family P) u) hQS hQesc
  rw [←hepsilon] at hR hQ
  exact ⟨hR,graph_radius_one_commutator_of_edge h he hQ⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
