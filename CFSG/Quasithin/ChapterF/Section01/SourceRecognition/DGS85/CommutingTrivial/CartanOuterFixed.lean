module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeBetaKernelSource
public import Theory.Representation.BinaryConjugationSection.NormalizerKernel
public import Theory.Representation.BinaryConjugationSection.SL2RegularLine

/-!
# Full Cartan action on the original central lines

The outer Cartan factor can lie in the full permutation kernel at the
terminal vertex. Its action is detected instead on the literal central
lines of the neighboring natural sections. A full local torus is regular
on each nonzero line, so an actor commuting with it fixes either the whole
line or only the identity. Trivial action on the whole residual section
forces full permutation-kernel membership, which the original path excludes.

Source: DGS, *Groups and Graphs* (1985), 5.1 and 9.10(4), pp.105,148.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A full edge actor centralizing the transitive local action modulo its
full kernel lies in that kernel. -/
theorem edge_actor_le_kernel_of_local_commutator
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (T : Subgroup G) (hTv : T ≤ stabilizer (family P) v)
    (hTw : T ≤ stabilizer (family P) w)
    (hc : ⁅T,graphLocalGroup (family P) v⁆ ≤ ballKernel (family P) v 1) :
    T ≤ ballKernel (family P) v 1 := by
  let := finite_endpoints h
  let Γ := family P
  intro t ht z hz
  rcases (mem_ball_one Γ v z).mp hz with hz | rfl
  · obtain ⟨g,hg,hgz⟩ := graphLocalGroup_transitive h hB hS v ⟨w,hvw⟩ ⟨z,hz⟩
    have hcomm : ⁅t,g⁆ • z = z := hc (commutator_mem_commutator ht hg) z
      ((mem_ball_one Γ v z).mpr (Or.inl hz))
    calc
      t • z = (t*g) • w := by rw [mul_smul,hgz]
      _ = (⁅t,g⁆*(g*t)) • w := by congr 1; group
      _ = ⁅t,g⁆ • (g • (t • w)) := by rw [mul_smul,mul_smul]
      _ = z := by rw [hTw ht,hgz,hcomm]
  · exact hTv ht

/-- Trivial action on the genuine faithful natural residual section detects
membership in the full permutation kernel. -/
theorem natural_residual_displacement_le_kernel
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {F : Type*} [Field F]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL(2,F) W) (hf : Function.Injective σ)
    (c : BinaryConjugationSection (graphLocalGroup (family P) v) (V (family P) v 1)
      (Z (family P) v) (σ.comp (e.toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) v))))))
    (T : Subgroup G)
    (hTv : T ≤ stabilizer (family P) v) (hTw : T ≤ stabilizer (family P) w)
    (hm : ⁅T,V (family P) v 1⁆ ≤ Z (family P) v) :
    T ≤ ballKernel (family P) v 1 := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hck := c.commutator_le_actor_kernel_of_displacement H (V Γ v 1) (Z Γ v) T q σ hf
    (hTv.trans (sylowGenerated_normalized _))
    (hTv.trans (stabilizer_normalizes_V Γ v 1)) hm
  have hcore : (pCore 2 H).map H.subtype = Q Γ v := graphLocalGroup_core h v
  rw [hk,hcore] at hck
  exact edge_actor_le_kernel_of_local_commutator h hB hS hvw T hTv hTw
    (hck.trans (source_Z_Q_U h v).2)

/-- On a central line of the original natural center, an abelian full
Cartan factor has either zero or full fixed subgroup. The cardinal and
natural-action inputs are the original source markings. -/
theorem natural_center_cartan_line_dichotomy
    (h : LocallyRankOneTriple P B) (a : Vertex (family P))
    {F : Type*} [Field F] [CharP F 2] [Finite F]
    (ea : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,F)) :
    letI := Z_elementary (family P) (fun v => (source_Z_Q_U h v).1) a
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    let H := graphLocalGroup (family P) a
    let q := ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    ∀ ρ : Representation (ZMod 2) SL(2,F) (Additive (Z (family P) a)),
      (∀ (l : H) (z : Additive (Z (family P) a)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      ∀ E : Additive (Z (family P) a) ≃ₗ[ZMod 2] (Fin 2 → F),
      (∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z)) →
      ∀ C R T : Subgroup G, IsMulCommutative C → Odd (Nat.card C) →
      C ≤ stabilizer (family P) a → T ≤ C →
      Nonempty ((C ⊓ H : Subgroup G) ≃* Fˣ) →
      R ≤ Z (family P) a → Nat.card R = Nat.card F →
      C ≤ normalizer (R : Set G) →
      R ⊓ centralizer (T : Set G) = ⊥ ∨ R ≤ centralizer (T : Set G) := by
  let := finite_endpoints h
  let := Z_elementary (family P) (fun v => (source_Z_Q_U h v).1) a
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  dsimp only
  intro ρ hact E hE C R T hCa hCo hC hTC he hR hcard hn
  let Γ := family P
  let H := graphLocalGroup Γ a
  let q := ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : IsMulCommutative C := hCa
  let : Finite C := Finite.of_injective (inclusion hC) (inclusion_injective _)
  let : Finite (C ⊓ H : Subgroup G) := Finite.of_injective
    (inclusion (show C ⊓ H ≤ C from inf_le_left)) (inclusion_injective _)
  let : Finite R := Finite.of_injective (inclusion (hR.trans (Z_le_stabilizer Γ a)))
    (inclusion_injective _)
  have hZH : Z Γ a ≤ H := ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
    (core_le_graphLocalGroup h a)
  let c := CommutingNontrivial.centerSection H (Z Γ a) hZH
    ((sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ a)) q ρ hact
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ ea.injective,QuotientGroup.ker_mk']
  have hcount : Nat.card (C ⊓ H : Subgroup G) + 1 = Nat.card R := by
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv,Nat.card_units,hcard]
    have hp : 0 < Nat.card F := Nat.card_pos
    omega
  exact BinaryConjugationSection.natural_line_fixed_dichotomy H (Z Γ a) ⊥ q
    (hk ▸ pCore_isPGroup) ρ c E hE (C ⊓ H) R T inf_le_right
    (hCo.of_dvd_nat (card_dvd_of_le (show C ⊓ H ≤ C from inf_le_left))) hR disjoint_bot_right
    hcount (inf_le_left.trans hn)
    (inf_le_left.trans ((le_centralizer C).trans (centralizer_le hTC)))

/-- The initial outer factor fixes no nonidentity element of the beta
central line. Its companion line is central in its original local group. -/
theorem graph_cartan_initial_line_fixed
    (h : LocallyRankOneTriple P B)
    {a beta l : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    {F W : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ea : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,F))
    (σ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection (graphLocalGroup (family P) a) (Z (family P) a) ⊥
      (σ.comp (ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) a))))))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (hE : ∀ g z, E (σ g z) = Matrix.mulVec g.val (E z))
    (C : Subgroup G) [IsMulCommutative C] (ho : Odd (Nat.card C))
    (hCa : C ≤ stabilizer (family P) a) (hCb : C ≤ stabilizer (family P) beta)
    (he : Nonempty ((C ⊓ graphLocalGroup (family P) a : Subgroup G) ≃* Fˣ))
    (hcard : Nat.card (Z (family P) beta) = Nat.card F)
    (hspan : Z (family P) a = Z (family P) beta ⊔ Z (family P) l)
    (hωl : Z (family P) l = omegaCenterIn (graphLocalGroup (family P) l))
    (hne : C ⊓ graphLocalGroup (family P) l ≠ ⊥)
    (hdis : Disjoint (C ⊓ graphLocalGroup (family P) l) (ballKernel (family P) a 1)) :
    Z (family P) beta ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G) = ⊥ := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ a
  let K := C ⊓ H
  let T := C ⊓ graphLocalGroup Γ l
  let q := ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : Finite C := Finite.of_injective (inclusion hCa) (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion (show K ≤ C from inf_le_left)) (inclusion_injective _)
  let : Finite (Z Γ beta) := Finite.of_injective (inclusion (Z_le_stabilizer Γ beta)) (inclusion_injective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ ea.injective,QuotientGroup.ker_mk']
  have hcount : Nat.card K + 1 = Nat.card (Z Γ beta) := by
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv,Nat.card_units,hcard]
    have hp : 0 < Nat.card F := Nat.card_pos
    omega
  have hba : Z Γ beta ≤ Z Γ a := hspan ▸ le_sup_left
  rcases BinaryConjugationSection.natural_line_fixed_dichotomy H (Z Γ a) ⊥ q
      (hk ▸ pCore_isPGroup) σ c E hE K (Z Γ beta) T inf_le_right
      (ho.of_dvd_nat (card_dvd_of_le (show K ≤ C from inf_le_left))) hba disjoint_bot_right
      hcount (inf_le_left.trans (hCb.trans (CommutingNontrivial.stabilizer_normalizes_Z Γ beta)))
      (inf_le_left.trans ((le_centralizer C).trans (centralizer_le (show T ≤ C from inf_le_left))))
    with hz | hz
  · exact hz
  have hl : Z Γ l ≤ centralizer (T : Set G) := by
    intro z hz
    exact centralizer_le (show T ≤ graphLocalGroup Γ l from inf_le_right)
      ((mem_omegaCenterIn_iff _ _).mp (hωl ▸ hz)).2.1
  have hTa : T ≤ stabilizer Γ a ⊓ centralizer (Z Γ a : Set G) := by
    refine le_inf (inf_le_left.trans hCa) ?_
    apply le_centralizer_iff.mpr
    rw [hspan]
    exact sup_le hz hl
  have hTk := hTa.trans (center_centralizer_le_kernel_of_neighbor_center h hab hba)
  exact (hne (disjoint_self.mp (hdis.mono_right hTk))).elim

/-- The terminal central line is fixed-free for the outer factor. A fixed
nonzero vector would force the entire line to be fixed; together with its
central companion this would make the original residual action trivial. -/
theorem graph_cartan_terminal_line_fixed
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta x a' l : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    {F W : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W]
    (eb : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (σ : Representation (ZMod 2) SL(2,F) W) (hf : Function.Injective σ)
    (c : BinaryConjugationSection (graphLocalGroup (family P) beta) (V (family P) beta 1)
      (Z (family P) beta) (σ.comp (eb.toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) beta))))))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (hE : ∀ g z, E (σ g z) = Matrix.mulVec g.val (E z))
    (C : Subgroup G) [IsMulCommutative C] (ho : Odd (Nat.card C))
    (hCa : C ≤ stabilizer (family P) a) (hCb : C ≤ stabilizer (family P) beta)
    (hCd : C ≤ stabilizer (family P) a')
    (he : Nonempty ((C ⊓ graphLocalGroup (family P) beta : Subgroup G) ≃* Fˣ))
    (hcard : Nat.card (Z (family P) a') = Nat.card F)
    (hspanA : Z (family P) a = Z (family P) beta ⊔ Z (family P) l)
    (hspanX : Z (family P) x = Z (family P) beta ⊔ Z (family P) a')
    (hspanV : V (family P) beta 1 = Z (family P) a ⊔ Z (family P) x)
    (hdisZ : Disjoint (Z (family P) beta) (Z (family P) a'))
    (hωl : Z (family P) l = omegaCenterIn (graphLocalGroup (family P) l))
    (hne : C ⊓ graphLocalGroup (family P) l ≠ ⊥)
    (hdis : Disjoint (C ⊓ graphLocalGroup (family P) l) (ballKernel (family P) beta 1)) :
    Z (family P) a' ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G) = ⊥ := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ beta
  let K := C ⊓ H
  let T := C ⊓ graphLocalGroup Γ l
  let q := eb.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : Finite C := Finite.of_injective (inclusion hCa) (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion (show K ≤ C from inf_le_left)) (inclusion_injective _)
  let : Finite (Z Γ a') := Finite.of_injective (inclusion (Z_le_stabilizer Γ a')) (inclusion_injective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ eb.injective,QuotientGroup.ker_mk']
  have hcount : Nat.card K + 1 = Nat.card (Z Γ a') := by
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv,Nat.card_units,hcard]
    have hp : 0 < Nat.card F := Nat.card_pos
    omega
  have haV : Z Γ a ≤ V Γ beta 1 := hspanV ▸ le_sup_left
  have hxV : Z Γ x ≤ V Γ beta 1 := hspanV ▸ le_sup_right
  have hbA : Z Γ beta ≤ Z Γ a := hspanA ▸ le_sup_left
  have hlA : Z Γ l ≤ Z Γ a := hspanA ▸ le_sup_right
  have hbX : Z Γ beta ≤ Z Γ x := hspanX ▸ le_sup_left
  have hdX : Z Γ a' ≤ Z Γ x := hspanX ▸ le_sup_right
  rcases BinaryConjugationSection.natural_line_fixed_dichotomy H (V Γ beta 1) (Z Γ beta) q
      (hk ▸ pCore_isPGroup) σ c E hE K (Z Γ a') T inf_le_right
      (ho.of_dvd_nat (card_dvd_of_le (show K ≤ C from inf_le_left)))
      (hdX.trans hxV) hdisZ.symm hcount
      (inf_le_left.trans (hCd.trans (CommutingNontrivial.stabilizer_normalizes_Z Γ a')))
      (inf_le_left.trans ((le_centralizer C).trans (centralizer_le (show T ≤ C from inf_le_left))))
    with hz | hz
  · exact hz
  have hl : Z Γ l ≤ centralizer (T : Set G) := by
    intro z hz
    exact centralizer_le (show T ≤ graphLocalGroup Γ l from inf_le_right)
      ((mem_omegaCenterIn_iff _ _).mp (hωl ▸ hz)).2.1
  have hn : V Γ beta 1 ≤ normalizer (Z Γ beta : Set G) := c.section_le.trans c.kernel_normalized
  have hbT : ⁅Z Γ beta,T⁆ ≤ Z Γ beta := le_normalizer_iff_commutator_le_left.mp
    (inf_le_left.trans (hCb.trans (CommutingNontrivial.stabilizer_normalizes_Z Γ beta)))
  have haT : ⁅Z Γ a,T⁆ ≤ Z Γ beta := by
    rw [hspanA]
    exact commutator_sup_le_of_relative_normal (V Γ beta 1) _ _ _ _ hn
      (hbA.trans haV) (hlA.trans haV) hbT
      ((commutator_eq_bot_iff_le_centralizer.mpr hl).le.trans bot_le)
  have hxT : ⁅Z Γ x,T⁆ ≤ Z Γ beta := by
    rw [hspanX]
    exact commutator_sup_le_of_relative_normal (V Γ beta 1) _ _ _ _ hn
      (hbX.trans hxV) (hdX.trans hxV) hbT
      ((commutator_eq_bot_iff_le_centralizer.mpr hz).le.trans bot_le)
  have hVT : ⁅T,V Γ beta 1⁆ ≤ Z Γ beta := by
    rw [commutator_comm,hspanV]
    exact commutator_sup_le_of_relative_normal (V Γ beta 1) _ _ _ _ hn haV hxV haT hxT
  have hTk := natural_residual_displacement_le_kernel h hB hS hab.symm eb σ hf c T
    (inf_le_left.trans hCb) (inf_le_left.trans hCa) hVT
  exact (hne (disjoint_self.mp (hdis.mono_right hTk))).elim

private theorem fixed_join_eq_bot
    (A B T : Subgroup G)
    (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G))
    (hnA : T ≤ normalizer (A : Set G)) (hnB : T ≤ normalizer (B : Set G))
    (hA : A ⊓ centralizer (T : Set G) = ⊥)
    (hB : B ⊓ centralizer (T : Set G) = ⊥) :
    (A ⊔ B) ⊓ centralizer (T : Set G) = ⊥ := by
  apply bot_unique
  rintro z ⟨hz,hzT⟩
  have hz' : z ∈ (A : Set G) * (B : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right A B (hc.trans (Subgroup.centralizer_le_normalizer _))]
    exact hz
  obtain ⟨a,ha,b,hb,rfl⟩ := hz'
  have hfix (t : G) (ht : t ∈ T) : t*a*t⁻¹ = a ∧ t*b*t⁻¹ = b := by
    have he : (t*a*t⁻¹)*(t*b*t⁻¹) = a*b := by
      calc
        _ = t*(a*b)*t⁻¹ := by group
        _ = a*b := mul_inv_eq_iff_eq_mul.mpr (hzT t ht)
    have hp : ((⟨t*a*t⁻¹,(mem_normalizer_iff.mp (hnA ht) a).mp ha⟩ : A),
        (⟨t*b*t⁻¹,(mem_normalizer_iff.mp (hnB ht) b).mp hb⟩ : B)) =
        ((⟨a,ha⟩ : A),(⟨b,hb⟩ : B)) := mul_injective_of_disjoint hd he
    exact ⟨congrArg (fun p : A × B => (p.1 : G)) hp,
      congrArg (fun p : A × B => (p.2 : G)) hp⟩
  have haT : a ∈ centralizer (T : Set G) := fun t ht => mul_inv_eq_iff_eq_mul.mp (hfix t ht).1
  have hbT : b ∈ centralizer (T : Set G) := fun t ht => mul_inv_eq_iff_eq_mul.mp (hfix t ht).2
  have ha1 : a = 1 := hA.le ⟨ha,haT⟩
  have hb1 : b = 1 := hB.le ⟨hb,hbT⟩
  simp only [ha1,hb1,one_mul,one_mem]

/-- The original outer fixed subgroup misses the terminal span. The two
literal natural sections exclude fixed points on both central summands of
`Z x`; the reciprocal span-core intersection then applies this to `D`.
This is the fixed-point conclusion of DGS 9.10(4). -/
theorem graph_cartan_outer_fixed_disjoint
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta x a' l : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    {F Wa Wb : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
    [AddCommGroup Wa] [Module (ZMod 2) Wa] [AddCommGroup Wb] [Module (ZMod 2) Wb]
    (ea : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,F))
    (eb : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (σa : Representation (ZMod 2) SL(2,F) Wa)
    (σb : Representation (ZMod 2) SL(2,F) Wb) (hfb : Function.Injective σb)
    (ca : BinaryConjugationSection (graphLocalGroup (family P) a) (Z (family P) a) ⊥
      (σa.comp (ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) a))))))
    (cb : BinaryConjugationSection (graphLocalGroup (family P) beta) (V (family P) beta 1)
      (Z (family P) beta) (σb.comp (eb.toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) beta))))))
    (Ea : Wa ≃ₗ[ZMod 2] (Fin 2 → F)) (Eb : Wb ≃ₗ[ZMod 2] (Fin 2 → F))
    (hEa : ∀ g z, Ea (σa g z) = Matrix.mulVec g.val (Ea z))
    (hEb : ∀ g z, Eb (σb g z) = Matrix.mulVec g.val (Eb z))
    (C : Subgroup G) [IsMulCommutative C] (ho : Odd (Nat.card C))
    (hCa : C ≤ stabilizer (family P) a) (hCb : C ≤ stabilizer (family P) beta)
    (hCd : C ≤ stabilizer (family P) a')
    (hea : Nonempty ((C ⊓ graphLocalGroup (family P) a : Subgroup G) ≃* Fˣ))
    (heb : Nonempty ((C ⊓ graphLocalGroup (family P) beta : Subgroup G) ≃* Fˣ))
    (hcardB : Nat.card (Z (family P) beta) = Nat.card F)
    (hcardD : Nat.card (Z (family P) a') = Nat.card F)
    (hspanA : Z (family P) a = Z (family P) beta ⊔ Z (family P) l)
    (hspanX : Z (family P) x = Z (family P) beta ⊔ Z (family P) a')
    (hspanV : V (family P) beta 1 = Z (family P) a ⊔ Z (family P) x)
    (hdisZ : Disjoint (Z (family P) beta) (Z (family P) a'))
    (hωl : Z (family P) l = omegaCenterIn (graphLocalGroup (family P) l))
    (hne : C ⊓ graphLocalGroup (family P) l ≠ ⊥)
    (hdisA : Disjoint (C ⊓ graphLocalGroup (family P) l) (ballKernel (family P) a 1))
    (hdisB : Disjoint (C ⊓ graphLocalGroup (family P) l) (ballKernel (family P) beta 1))
    (hDQ : Q (family P) l ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G) ≤
      Q (family P) beta)
    (hVQ : V (family P) a' 1 ⊓ Q (family P) beta = Z (family P) x) :
    Disjoint (Q (family P) l ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G))
      (V (family P) a' 1) := by
  let := finite_endpoints h
  let Γ := family P
  let T := C ⊓ graphLocalGroup Γ l
  let := Z_elementary Γ (fun v => (source_Z_Q_U h v).1) x
  have hfixB := graph_cartan_initial_line_fixed h hab ea σa ca Ea hEa C ho hCa hCb
    hea hcardB hspanA hωl hne hdisA
  have hfixD := graph_cartan_terminal_line_fixed h hB hS hab eb σb hfb cb Eb hEb C ho
    hCa hCb hCd heb hcardD hspanA hspanX hspanV hdisZ hωl hne hdisB
  have hbX : Z Γ beta ≤ Z Γ x := hspanX ▸ le_sup_left
  have hdX : Z Γ a' ≤ Z Γ x := hspanX ▸ le_sup_right
  have hfixX : Z Γ x ⊓ centralizer (T : Set G) = ⊥ := by
    rw [hspanX]
    exact fixed_join_eq_bot _ _ _ hdisZ
      (hbX.trans ((le_centralizer (Z Γ x)).trans (centralizer_le hdX)))
      (inf_le_left.trans (hCb.trans (CommutingNontrivial.stabilizer_normalizes_Z Γ beta)))
      (inf_le_left.trans (hCd.trans (CommutingNontrivial.stabilizer_normalizes_Z Γ a')))
      hfixB hfixD
  apply disjoint_iff.mpr
  apply bot_unique
  rintro z ⟨hzD,hzV⟩
  exact hfixX.le ⟨hVQ ▸ (show z ∈ V Γ a' 1 ⊓ Q Γ beta from ⟨hzV,hDQ hzD⟩),hzD.2⟩

/-- The literal source-field version of outer disjointness retains the
independent alpha and beta markings and coordinates. Equality of the field
orders is used only for the initial central-line cardinality. -/
theorem graph_cartan_outer_fixed_disjoint_of_fields
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta x a' l : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    {F K Wa Wb : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
    [Field K] [CharP K 2] [Finite K] [Algebra (ZMod 2) K]
    (hKF : Nat.card K = Nat.card F)
    [AddCommGroup Wa] [Module (ZMod 2) Wa] [AddCommGroup Wb] [Module (ZMod 2) Wb]
    (ea : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,K))
    (eb : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (σa : Representation (ZMod 2) SL(2,K) Wa)
    (σb : Representation (ZMod 2) SL(2,F) Wb) (hfb : Function.Injective σb)
    (ca : BinaryConjugationSection (graphLocalGroup (family P) a) (Z (family P) a) ⊥
      (σa.comp (ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) a))))))
    (cb : BinaryConjugationSection (graphLocalGroup (family P) beta) (V (family P) beta 1)
      (Z (family P) beta) (σb.comp (eb.toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) beta))))))
    (Ea : Wa ≃ₗ[ZMod 2] (Fin 2 → K)) (Eb : Wb ≃ₗ[ZMod 2] (Fin 2 → F))
    (hEa : ∀ g z, Ea (σa g z) = Matrix.mulVec g.val (Ea z))
    (hEb : ∀ g z, Eb (σb g z) = Matrix.mulVec g.val (Eb z))
    (C : Subgroup G) [IsMulCommutative C] (ho : Odd (Nat.card C))
    (hCa : C ≤ stabilizer (family P) a) (hCb : C ≤ stabilizer (family P) beta)
    (hCd : C ≤ stabilizer (family P) a')
    (hea : Nonempty ((C ⊓ graphLocalGroup (family P) a : Subgroup G) ≃* Kˣ))
    (heb : Nonempty ((C ⊓ graphLocalGroup (family P) beta : Subgroup G) ≃* Fˣ))
    (hcardB : Nat.card (Z (family P) beta) = Nat.card F)
    (hcardD : Nat.card (Z (family P) a') = Nat.card F)
    (hspanA : Z (family P) a = Z (family P) beta ⊔ Z (family P) l)
    (hspanX : Z (family P) x = Z (family P) beta ⊔ Z (family P) a')
    (hspanV : V (family P) beta 1 = Z (family P) a ⊔ Z (family P) x)
    (hdisZ : Disjoint (Z (family P) beta) (Z (family P) a'))
    (hωl : Z (family P) l = omegaCenterIn (graphLocalGroup (family P) l))
    (hne : C ⊓ graphLocalGroup (family P) l ≠ ⊥)
    (hdisA : Disjoint (C ⊓ graphLocalGroup (family P) l) (ballKernel (family P) a 1))
    (hdisB : Disjoint (C ⊓ graphLocalGroup (family P) l) (ballKernel (family P) beta 1))
    (hDQ : Q (family P) l ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G) ≤
      Q (family P) beta)
    (hVQ : V (family P) a' 1 ⊓ Q (family P) beta = Z (family P) x) :
    Disjoint (Q (family P) l ⊓ centralizer (C ⊓ graphLocalGroup (family P) l : Set G))
      (V (family P) a' 1) := by
  let := finite_endpoints h
  let Γ := family P
  let T := C ⊓ graphLocalGroup Γ l
  let := Z_elementary Γ (fun v => (source_Z_Q_U h v).1) x
  have hfixB := graph_cartan_initial_line_fixed h hab ea σa ca Ea hEa C ho hCa hCb
    hea (hcardB.trans hKF.symm) hspanA hωl hne hdisA
  have hfixD := graph_cartan_terminal_line_fixed h hB hS hab eb σb hfb cb Eb hEb C ho
    hCa hCb hCd heb hcardD hspanA hspanX hspanV hdisZ hωl hne hdisB
  have hbX : Z Γ beta ≤ Z Γ x := hspanX ▸ le_sup_left
  have hdX : Z Γ a' ≤ Z Γ x := hspanX ▸ le_sup_right
  have hfixX : Z Γ x ⊓ centralizer (T : Set G) = ⊥ := by
    rw [hspanX]
    exact fixed_join_eq_bot _ _ _ hdisZ
      (hbX.trans ((le_centralizer (Z Γ x)).trans (centralizer_le hdX)))
      (inf_le_left.trans (hCb.trans (CommutingNontrivial.stabilizer_normalizes_Z Γ beta)))
      (inf_le_left.trans (hCd.trans (CommutingNontrivial.stabilizer_normalizes_Z Γ a')))
      hfixB hfixD
  apply disjoint_iff.mpr
  apply bot_unique
  rintro z ⟨hzD,hzV⟩
  exact hfixX.le ⟨hVQ ▸ (show z ∈ V Γ a' 1 ⊓ Q Γ beta from ⟨hzV,hDQ hzD⟩),hzD.2⟩


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
