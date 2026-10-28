module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ModulePreparation
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator
public import Theory.Representation.BinaryConjugationSection.FixedQuotientIndex

/-!
# The actual quadratic actor at a moving neighbor

The nontrivial displacement in 8.0 detects a neighbor lambda of alpha'.
The actor A = V_beta intersect Q_alpha' lies in both marked edge Sylows.
The already proved mutual quadratic action restricts to Z_lambda, and the
central omega equality at alpha' makes L_lambda centerless. Thus the same
Sylow-fixed generation and two-residual fixed-space argument applies to
Z_lambda. Its coordinates are the identity on the original center.

Containment of every full-vertex Sylow in L also proves that O2(L), embedded
in the completion, equals Q. Consequently the literal quotient actor has
order [A : A intersect Q_lambda] and is nontrivial. `MovingApplication`
uses this exact actor and action in corrected 5.12.

Source: DGS, *Groups and Graphs* (1985), 8.0--8.1, pp.132--134.
This proves the module premises; faithfulness, local generation and quotient
Sylow-center displacement remain separate Chapter 8 obligations.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

/-- The equivariant local family is normal in each full stabilizer. -/
theorem localGroup_normalized (F : Bool → Subgroup G) (d : EarlierLocalTheorems F)
    (v : Vertex F) : stabilizer F v ≤ normalizer (d.localGroup v : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (d.localGroup v).map (MulAut.conj g).toMonoidHom = _
  rw [← d.conjugate]
  exact congrArg d.localGroup hg

/-- Containment of every full-vertex Sylow places every two-subgroup in L. -/
theorem pGroup_le_localGroup (F : Bool → Subgroup G) (d : EarlierLocalTheorems F)
    (v : Vertex F) (A : Subgroup G) (hA : IsPGroup 2 A)
    (hAP : A ≤ stabilizer F v) : A ≤ d.localGroup v := by
  have hp : IsPGroup 2 (A.subgroupOf (stabilizer F v)) := hA.comap_subtype
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  intro x hx
  exact d.sylow_le v T (mem_map_of_mem _ (hT (show
    (⟨x, hAP hx⟩ : stabilizer F v) ∈ A.subgroupOf (stabilizer F v) from hx)))

/-- The embedded core denominator of L is the original vertex core Q. -/
theorem localGroup_core_eq (F : Bool → Subgroup G) (d : EarlierLocalTheorems F)
    (v : Vertex F) : (d.localGroup v).pCoreIn 2 = Q F v := by
  apply le_antisymm (pCoreIn_mono_of_normalizes (d.local_le v) (localGroup_normalized F d v))
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (stabilizer F v))
    (pGroup_le_localGroup F d v _ (isPGroup_pCoreIn 2 _) (Q_le_stabilizer F v))
    ((d.local_le v).trans (stabilizer_normalizes_Q F v))

/-- A marked conjugation action on the original elementary center has identity
coordinates and trivial vector denominator. -/
def centerSection {D : Type*} [Group D] (L Z : Subgroup G)
    [IsElementaryAbelian 2 Z] (hZL : Z ≤ L) (hn : L ≤ normalizer (Z : Set G))
    (q : L →* D) (ρ : Representation (ZMod 2) D (Additive Z))
    (hact : ∀ (l : L) (z : Additive Z),
      ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) :
    BinaryConjugationSection L Z ⊥ (ρ.comp q) where
  section_le := hZL
  kernel_le := bot_le
  normalized := hn
  coordinates := { toFun := fun z => Multiplicative.ofAdd (Additive.ofMul z)
                   map_one' := rfl
                   map_mul' := fun _ _ => rfl }
  onto := fun z => ⟨z.toAdd.toMul, rfl⟩
  kernel_eq := by
    ext z
    change z = 1 ↔ (z : G) = 1
    exact ⟨fun hz => congrArg Z.subtype hz, fun hz => Subtype.ext hz⟩
  equivariant l z := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (hact l (Additive.ofMul z)).symm

/-- The quotient map has precisely the original embedded core as kernel. -/
theorem local_quotient_kernel (F : Bool → Subgroup G) (d : EarlierLocalTheorems F)
    (v : Vertex F) {D : Type*} [Group D]
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* D) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup v)))).ker =
      (Q F v).subgroupOf (d.localGroup v) := by
  ext l
  change e (QuotientGroup.mk' (pCore 2 (d.localGroup v)) l) = 1 ↔ (l : G) ∈ Q F v
  rw [← e.map_one, e.injective.eq_iff]
  change l ∈ (QuotientGroup.mk' (pCore 2 (d.localGroup v))).ker ↔ _
  rw [QuotientGroup.ker_mk', ← localGroup_core_eq F d v]
  exact ⟨mem_map_of_mem _, fun ⟨k, hk, he⟩ => (Subtype.ext he : k = l) ▸ hk⟩

/-- The moving neighbor in 8.0 carries a nontrivial quadratic actor, inside an
actual common edge Sylow. Its local group is centerless by 8.1(b) at that edge. -/
theorem source_moving_actor
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥) :
    let F := family P
    let A := V F beta 1 ⊓ Q F a'
    center (d.localGroup w.val) = ⊥ ∧ A ≤ d.localGroup w.val ∧
      ⁅A, ⁅A, Z F w.val⁆⁆ = ⊥ ∧ ¬ A ≤ Q F w.val ∧
      ∃ (T : Sylow 2 (stabilizer F w.val)) (R : Sylow 2 (stabilizer F a')),
        (T : Subgroup (stabilizer F w.val)).map (stabilizer F w.val).subtype =
          (R : Subgroup (stabilizer F a')).map (stabilizer F a').subtype ∧
        A ≤ (T : Subgroup (stabilizer F w.val)).map (stabilizer F w.val).subtype := by
  dsimp only
  let := finite_endpoints h
  have hZ := fun v => (source_Z_Q_U h v).1
  have hQU := fun v => (source_Z_Q_U h v).2
  have hend := critical_end_center_of_commuting (family P) h.generate hZ hQU hc hcomm
    (d.localGroup a') (d.sylow_or_center a')
  have hz := local_center_eq_bot_of_neighbor_central h d w.property.symm hend
  obtain ⟨_, _, _, hquad, _⟩ := source_critical_geometry h d hc hab hd hb hcomm
  obtain ⟨T, R, hTR⟩ := d.common_sylow w.val a' w.property.symm
  have hAT : V (family P) beta 1 ⊓ Q (family P) a' ≤
      (T : Subgroup (stabilizer (family P) w.val)).map (stabilizer (family P) w.val).subtype := by
    rw [hTR]
    exact inf_le_right.trans (pCoreIn_le_sylow _ R)
  refine ⟨hz, hAT.trans (d.sylow_le w.val T), ?_, ?_, T, R, hTR, hAT⟩
  · rw [commutator_comm (V (family P) beta 1 ⊓ Q (family P) a')]
    exact eq_bot_iff.mpr ((commutator_mono
      (commutator_mono inf_le_left (Z_neighbor_le_V (family P) w.property))
      inf_le_left).trans hquad.1.le)
  · intro hAQ
    exact hm (commutator_eq_bot_iff_le_centralizer.mpr
      (hAQ.trans (le_centralizer_iff.mp (Z_centralizes_Q (family P) w.val (hZ w.val)))))

/-- On the moving neighbor's original center, the actual image actor is
nontrivial, quadratic, and contained in the specified quotient Sylow. Both
supplementary premises of corrected 5.12 are proved on the same vectors. -/
theorem source_moving_center_module
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥)
    {D : Type*} [Group D]
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* D) :
    letI := CommutingOneProfile.source_center_elementary h w.val
    let F := family P
    let A := V F beta 1 ⊓ Q F a'
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup w.val)))
    let Aq := (A.subgroupOf (d.localGroup w.val)).map q
    ∃ (ρ : Representation (ZMod 2) D (Additive (Z F w.val))) (S : Sylow 2 D),
      (∀ (l : d.localGroup w.val) (z : Additive (Z F w.val)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) ∧
      Aq ≤ S ∧ Aq ≠ ⊥ ∧ IsQuadratic ρ Aq ∧
      GeneratedByFixedSpace ρ S ∧ fixedSpace ρ (pResidual 2 D) = ⊥ ∧
      Nat.card Aq = (Q F w.val).relIndex A := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h w.val
  dsimp only
  let F := family P
  let A := V F beta 1 ⊓ Q F a'
  let L := d.localGroup w.val
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  obtain ⟨hz, hAL, hquad, hescape, T, R, hTR, hAT⟩ :=
    source_moving_actor h d hc hab hd hb hcomm w hm
  obtain ⟨ρ, hact⟩ := source_exists_center_quotient_action h d w.val e
  obtain ⟨S, hS, hgen, hfix⟩ := source_center_module_prepared_of_center_eq_bot h d w.val hz T e ρ hact
  have hqker := local_quotient_kernel F d w.val e
  have hZL : Z F w.val ≤ L := pGroup_le_localGroup F d w.val _
    (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer F w.val)
  let c := centerSection L (Z F w.val) hZL
    ((d.local_le w.val).trans (stabilizer_normalizes_Z F w.val)) q ρ hact
  refine ⟨ρ, S, hact, ?_, ?_, ?_, hgen, hfix, ?_⟩
  · rw [hS]
    rintro _ ⟨l, hl, rfl⟩
    have ht : (⟨l, d.local_le w.val l.property⟩ : stabilizer F w.val) ∈ T := by
      obtain ⟨t, ht, he⟩ := hAT hl
      exact (Subtype.ext he : t = ⟨l, d.local_le w.val l.property⟩) ▸ ht
    exact ⟨⟨⟨l, d.local_le w.val l.property⟩, l.property⟩, ht, rfl⟩
  · intro he
    apply hescape
    intro x hx
    have hmem : q (⟨x, hAL hx⟩ : L) ∈ (A.subgroupOf L).map q :=
      mem_map_of_mem q hx
    have hk : (⟨x, hAL hx⟩ : L) ∈ q.ker := mem_bot.mp (he ▸ hmem)
    change (⟨x, hAL hx⟩ : L) ∈ (Q F w.val).subgroupOf L
    exact hqker ▸ hk
  · exact BinaryConjugationSection.isQuadratic_of_triple_commutator_le
      L (Z F w.val) ⊥ A ρ q c hquad.le
  · exact BinaryConjugationSection.actor_image_card_eq_relIndex L (Q F w.val) A q hqker hAL

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
