module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.BetaKernelDisplacement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.TwoKernelExchange
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.PathCartanExtension

/-!
# The remaining full-kernel exclusion for the extended Cartan

The beta-kernel intersection of the preceding torus moves V_beta into
Z_beta. It therefore fixes the other central neighbor line Z_alpha-prime.
Transport of the original natural alpha action shows that this odd subgroup
meets L_(alpha+2) trivially. Hall conjugacy now constructs an actual centralizing
exchange of beta and alpha-prime. The displacement then lies in two disjoint
central neighbor lines, so the original alpha-plus-two kernel exclusion
forces the subgroup to be trivial.

Both full permutation kernels are retained. No middle-kernel membership
is used in constructing the exchange.
Source: DGS, *Groups and Graphs* (1985), 9.10(3), printed p.148.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- An odd actor fixing a nonzero natural-center vector avoids the intrinsic local group,
including after transport along the original graph action. -/
theorem natural_center_odd_centralizer_disjoint
    (h : LocallyRankOneTriple P B) {a x : Vertex (family P)}
    {F : Type*} [Field F] [CharP F 2]
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
      ∀ g : G, g • x = a →
      ∀ D W : Subgroup G, Odd (Nat.card D) → W ≤ Z (family P) x → W ≠ ⊥ →
        D ≤ centralizer (W : Set G) → Disjoint D (graphLocalGroup (family P) x) := by
  let := finite_endpoints h
  let := Z_elementary (family P) (fun v => (source_Z_Q_U h v).1) a
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let Γ := family P
  let H := graphLocalGroup Γ a
  let q := ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  dsimp only
  intro ρ hact E hE g hg D W ho hWZ hWne hDW
  obtain ⟨w,hw,hwne⟩ := W.bot_or_exists_ne_one.resolve_left hWne
  let f := (MulAut.conj g).toMonoidHom
  have hwZ : f w ∈ Z Γ a := by
    rw [←hg,Z_translate]
    exact mem_map_of_mem f (hWZ hw)
  let z : Additive (Z Γ a) := Additive.ofMul ⟨f w,hwZ⟩
  have hz : E z ≠ 0 := by
    intro he
    have hz0 : z = 0 := E.injective (he.trans E.map_zero.symm)
    have he' : f w = 1 := congrArg (fun y : Additive (Z Γ a) => (y.toMul : G)) hz0
    exact hwne ((MulAut.conj g).injective (he'.trans (map_one f).symm))
  apply disjoint_def.mpr
  intro d hd hdH
  have hlH : f d ∈ H := by
    change f d ∈ graphLocalGroup Γ a
    rw [←hg,graphLocalGroup_conjugate h]
    exact mem_map_of_mem f hdH
  let l : H := ⟨f d,hlH⟩
  have hodd : Odd (orderOf l) := by
    rw [Subgroup.orderOf_mk]
    change Odd (orderOf ((MulAut.conj g) d))
    rw [MulEquiv.orderOf_eq]
    simpa only [Subgroup.orderOf_mk] using
      ho.of_dvd_nat (_root_.orderOf_dvd_natCard (⟨d,hd⟩ : D))
  have hfix : ρ (q l) z = z := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hact]
    apply mul_inv_eq_iff_eq_mul.mpr
    change f d * f w = f w * f d
    have hh := congrArg f (hDW hd w hw)
    simpa only [map_mul] using hh.symm
  have hq : q l = 1 := by
    by_contra hn
    apply hz
    apply Matrix.SL2.odd_power_fixed_eq_zero (q l) (orderOf l) hodd
      (by rw [←map_pow,pow_orderOf_eq_one,map_one]) hn
    rw [←hE,hfix]
  have hl : l ∈ pCore 2 H := (QuotientGroup.eq_one_iff l).mp
    (ea.injective (hq.trans ea.map_one.symm))
  have hc := (pCore_isPGroup (p := 2) (G := H)).orderOf_coprime
    hodd.coprime_two_left (⟨l,hl⟩ : pCore 2 H)
  have hc' : Nat.Coprime (orderOf (f d)) (orderOf (f d)) := by
    simpa only [l,Subgroup.orderOf_mk] using hc
  apply (MulAut.conj g).injective
  exact (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc' dvd_rfl dvd_rfl)).trans
    (map_one f).symm


variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The same full extended Cartan satisfies the beta-kernel exclusion in 9.10(3). -/
theorem reduced_extended_cartan_beta_kernel_disjoint
    (h : HypothesisF11 L S)
    {a beta x a' l : Vertex (Reduction.reducedFamily L S)}
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hbx : (graph (Reduction.reducedFamily L S)).Adj beta x)
    (hxa' : (graph (Reduction.reducedFamily L S)).Adj x a')
    (hne : beta ≠ a')
    (hω : Z (Reduction.reducedFamily L S) beta =
      omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S) beta))
    {F : Type*} [Field F] [CharP F 2] [Finite F]
    (ea : (graphLocalGroup (Reduction.reducedFamily L S) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) a)) ≃* SL(2,F)) :
    let Γ := Reduction.reducedFamily L S
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    let H := graphLocalGroup Γ a
    let q := ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    ∀ ρ : Representation (ZMod 2) SL(2,F) (Additive (Z Γ a)),
      (∀ (k : H) (z : Additive (Z Γ a)),
        ((ρ (q k) z).toMul : Reduction.G₀ L S) =
          (k : Reduction.G₀ L S) * z.toMul * (k : Reduction.G₀ L S)⁻¹) →
      ∀ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → F),
      (∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z)) →
      ∀ C : Subgroup (Reduction.G₀ L S), IsMulCommutative C → Odd (Nat.card C) →
        C ≤ stabilizer Γ a ⊓ stabilizer Γ beta ⊓ stabilizer Γ x ⊓ stabilizer Γ a' →
        Disjoint C ((stabilizer Γ a ⊓ stabilizer Γ beta : Subgroup (Reduction.G₀ L S)).pCoreIn 2) →
        C ⊔ (stabilizer Γ a ⊓ stabilizer Γ beta : Subgroup (Reduction.G₀ L S)).pCoreIn 2 =
          stabilizer Γ a ⊓ stabilizer Γ beta →
        C ⊓ graphLocalGroup Γ l = C ⊓ ballKernel Γ a' 1 →
        Disjoint (C ⊓ graphLocalGroup Γ l) (ballKernel Γ x 1) →
        ⁅V Γ beta 1,(C ⊓ graphLocalGroup Γ l) ⊓ ballKernel Γ beta 1⁆ ≤ Z Γ beta →
        Disjoint (C ⊓ graphLocalGroup Γ l) (ballKernel Γ beta 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  dsimp only
  intro ρ hact E hE C hCa ho hfix hdis hgen hker hdisx hdisp
  let : IsMulCommutative C := hCa
  let D := C ⊓ (ballKernel Γ beta 1 ⊓ ballKernel Γ a' 1)
  have hD : D = (C ⊓ graphLocalGroup Γ l) ⊓ ballKernel Γ beta 1 := by
    rw [hker]
    dsimp only [D]
    ac_rfl
  have hDC : D ≤ C := inf_le_left
  have hDa' : D ≤ stabilizer Γ a' := hDC.trans (hfix.trans inf_le_right)
  have hDx : D ≤ stabilizer Γ x := hDC.trans (hfix.trans (inf_le_left.trans inf_le_right))
  have hVD : ⁅V Γ beta 1,D⁆ ≤ Z Γ beta := hD.symm ▸ hdisp
  have hωa' : Z Γ a' = omegaCenterIn (graphLocalGroup Γ a') := by
    obtain ⟨g,_,hg⟩ := locally_transitive Γ hbx.symm hxa'
    have hh := graphLocalGroup_conjugate ht g beta
    change graphLocalGroup Γ (g • beta) =
      (graphLocalGroup Γ beta).map (MulAut.conj g).toMonoidHom at hh
    rw [←hg,Z_translate,hh,
      ←NilesRankOneKernel.omegaCenterIn_map_injective
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,hω]
  have ha'x : Z Γ a' ≤ Z Γ x := hωa' ▸ intrinsic_local_omega_le_neighbor_Z ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hxa'.symm
  have hline : Disjoint (Z Γ beta) (Z Γ a') :=
    Reduction.reduced_intrinsic_central_neighbor_centers_disjoint h hbx.symm hxa' hne hω
  have hDa'C : D ≤ centralizer (Z Γ a' : Set (Reduction.G₀ L S)) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    apply (le_inf
      ((commutator_mono (ha'x.trans (CommutingNontrivial.Z_neighbor_le_V Γ hbx)) le_rfl).trans hVD)
      (le_normalizer_iff_commutator_le_left.mp
        (hDa'.trans (CommutingNontrivial.stabilizer_normalizes_Z Γ a')))).trans
    exact (disjoint_iff.mp hline).le
  have hZa'ne : Z Γ a' ≠ ⊥ := by
    obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base Γ a'
    intro hbot
    have he : (Z Γ (base Γ a'.type)).map (MulAut.conj g).toMonoidHom = ⊥ := by
      rw [←Z_translate,hg]
      exact hbot
    exact base_Z_ne_bot ht _ ((map_eq_bot_iff_of_injective
      (f := (MulAut.conj g).toMonoidHom) _ (MulAut.conj g).injective).mp he)
  obtain ⟨g,_,hga⟩ := locally_transitive Γ hbx hab.symm
  have hDL : Disjoint D (graphLocalGroup Γ x) :=
    natural_center_odd_centralizer_disjoint ht ea ρ hact E hE g hga D (Z Γ a')
      (ho.of_dvd_nat (card_dvd_of_le hDC)) ha'x hZa'ne hDa'C
  obtain ⟨_,e,_,_,_⟩ := local_quotient_parameter_transport ht g hga
  have hCxb : C ≤ stabilizer Γ x ⊓ stabilizer Γ beta := le_inf
    (hfix.trans (inf_le_left.trans inf_le_right))
    (hfix.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
  obtain ⟨_,hgenx⟩ := path_cartan_complement_at_edge ht hab hbx.symm C
    (hfix.trans (inf_le_left.trans inf_le_left)) hCxb ho hdis hgen
  obtain ⟨t,htC,htb,_⟩ := full_cartan_two_kernel_centralizing_exchange ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hbx.symm hxa' (e.trans ea) C hCxb (hfix.trans inf_le_right) ho hgenx hDL
  apply disjoint_iff.mpr
  rw [←hD]
  exact reduced_beta_kernel_eq_bot_of_centralizing_exchange h hbx hxa' hne hω D hDx hVD
    (hdisx.mono_left (hD.le.trans inf_le_left)) t htC.2 htb

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
