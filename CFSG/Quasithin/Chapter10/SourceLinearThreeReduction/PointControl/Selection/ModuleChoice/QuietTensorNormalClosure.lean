module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorAutomizer
public import Theory.GroupTheory.RelativeSylowFrattini

/-!
# The actual tensor point normal closure and relative Frattini product

The Chapter1 detection theorem gives an orbit normal in C_G(z) and fully
moved by the original cubic complement P. Its normality bounds the literal
K_z=⟨X^{C_G(z)}⟩ from above; the commutator identity bounds it from below.
Thus the same K_z equals X or the detected component orbit, with the original
model isomorphisms and the adequate Held alternative retained.

The actual section centralizer Y_z is normal in N_{G_z}(X) and has the
original S=O₂(XT) as Sylow subgroup. Relative Frattini factorization and
N_G(S)≤M give N_{G_z}(X)=Y_z(N_{G_z}(X)∩M). In the normal-X branch this
is G_z=Y_z M_z. The solvable-Y_z branch lies in M by the proved 8.3.6.

The remaining model exclusions, conjugacy argument, and nonsolvable-Y_z
containment still need source proofs before asserting G_z=K_z M_z.
Tensor-base recognition and the remaining quiet fixed-support obligations
stay with the selected-module owner; final point-control assembly stays
with qt-d-10-nona5-point-control. Source: Aschbacher--Smith 8.3.7,
printed pp.724--725, using the corrected intrinsic 1.3.4 alternatives.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
universe u
open Chapter3.Section02 ChapterE Chapter8.Section03
open Chapter1.XiEmbedding
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem detected_normalClosure {T X P H K : Subgroup G}
    (h : LocalInput 3 T X P H) (hK : ComponentDetection P H K)
    (hn : ((componentOrbit K T).subgroupOf H).Normal)
    (hc : ⁅componentOrbit K T,P⁆ = componentOrbit K T)
    (hX : X ≤ componentOrbit K T) :
    conjugateSpanBy X H = componentOrbit K T := by
  have hOH : componentOrbit K T ≤ H :=
    (componentOrbit_le_sup K T).trans
      (sup_le hK.mem.1 (le_sup_right.trans h.overgroup))
  have hNX : H ≤ normalizer (conjugateSpanBy X H : Set G) :=
    le_normalizer_conjugateSpanBy X H
  apply le_antisymm
  · exact conjugateSpanBy_le hX ((normal_subgroupOf_iff_le_normalizer hOH).mp hn)
  · rw [←hc]
    exact (commutator_mono le_rfl
      ((le_sup_right.trans h.complement.le).trans (le_conjugateSpanBy X H))).trans
      (le_normalizer_iff_commutator_le_right.mp (hOH.trans hNX))

private theorem detected_alternatives {T X P H : Subgroup G}
    (h : LocalInput 3 T X P H) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hT : Chapter1.IsSylowIn 2 T H) :
    conjugateSpanBy X H = X ∨ ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn H ∧ IsQuasisimple (Chapter1.XiQuotient K) ∧
      conjugateSpanBy X H = componentOrbit K T ∧
      ⁅componentOrbit K T,P⁆ = componentOrbit K T ∧
      (Alternatives 3 T P K ∨ HeldAlternative 3 T P K) := by
  let hA := fun (Y : Type u) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type u) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremC_knownSimple (G := Y)
  rcases h.normal_or_detected_containment hA hC hH hT with
    hn | ⟨K,hK,hn,hcomm,hP,hX⟩
  · exact Or.inl (le_antisymm (conjugateSpanBy_le le_rfl
      ((normal_subgroupOf_iff_le_normalizer (le_sup_left.trans h.overgroup)).mp hn))
      (le_conjugateSpanBy X H))
  · refine Or.inr ⟨K,hK.mem,hK.quasisimple,
      detected_normalClosure h hK hn hcomm hX,hcomm,?_⟩
    by_cases hi : T ≤ normalizer K
    · have horbit : componentOrbit K T = K :=
        le_antisymm (iSup_conjugates_le_of_le_normalizer K T K le_rfl hi)
          (le_componentOrbit K T)
      rw [horbit] at hn hcomm hP
      exact InvariantThree.Source.alternatives_knownSimple h hH hT hK.mem.1 hn
        hK.quasisimple hP hcomm
    · let hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 T X P H K :=
        { toLocalInput := h
          sqtk := hH
          component := hK.mem
          quasisimple := hK.quasisimple
          orbit_normal := hn
          complement_le_orbit := hP
          orbit_commutator := hcomm
          noncentral := hK.noncentral_component_core
          not_invariant := hi
          sylow_two := hT }
      obtain ⟨he,hf,hm⟩ := SwappedSylow.embedding_of_theoremsAC hA hC hs
      exact Or.inl ⟨he,Or.inl ⟨hf,hm⟩⟩

variable {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
private instance : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Multiplicative.toAdd.injective
    ext i
    change (3 : ℕ) • x.toAdd i = 0
    exact (show ∀ a : ZMod 3, (3 : ℕ) • a = 0 by decide) _

/-- The actual normal closure K_z is X or the detected component orbit.
The same original cubic complement moves the whole orbit; every remaining
model alternative, including Held, is retained. -/
theorem quiet_tensor_point_normalClosure_alternatives
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let P₀ := (P : Subgroup d.X).map d.X.subtype
    d.Kz = d.X ∨ ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn d.Gz ∧ IsQuasisimple (Chapter1.XiQuotient K) ∧
      d.Kz = componentOrbit K (T : Subgroup G) ∧ ⁅d.Kz,P₀⁆ = d.Kz ∧
      Nonempty (P₀ ≃* Plane 3) ∧
      ((SwappedFactors (T : Subgroup G) P₀ K ∧ SwappedModel 3 (Chapter1.XiQuotient K)) ∨
        ((T : Subgroup G) ≤ normalizer (K : Set G) ∧
          (LinearThreeModel 3 (Chapter1.XiQuotient K) ∨
            ExceptionalModel (Chapter1.XiQuotient K) ∨
            Nonempty (Chapter1.XiQuotient K ≃* Held.He)))) := by
  dsimp only
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hXi := quiet_tensor_point_residual_mem_Xi D hn e hbase hzV hz1 hzT
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) d.Gz :=
    ⟨T.subtype hzT,map_subgroupOf_eq_of_le hzT⟩
  have hXT : d.XT ≤ d.Gz := sup_le (d.X_le.trans inf_le_right) hzT
  obtain ⟨c⟩ := quiet_tensor_point_residual_quotient D hn e hbase hzV hz1 hzT
  have hq : Chapter1.XiOddQuotient 3 (Chapter1.XiQuotient d.X) := by
    refine Or.inl ⟨IsElementaryAbelian.of_injective c.toMonoidHom c.injective,?_⟩
    rw [Nat.card_congr c.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  have hlocal : IsTwoLocal d.Gz := isTwoLocal_involution_centralizer hz2
  have hi := Chapter1.XiEmbedding.localInput_of_mem_Xi hXi hT hXT (by decide) hq P
  have hnc := quiet_tensor_point_automizer_not_cyclic D hn e hbase hzV hz1 hzT P
  rcases detected_alternatives hi (D.simpleQTKE.twoLocal_sqtk hlocal) hT with
    hnormal | ⟨K,hK,hquasi,hclosure,hcomm,hrows⟩
  · exact Or.inl hnormal
  · refine Or.inr ⟨K,hK,hquasi,hclosure,?_,?_⟩
    · change ⁅conjugateSpanBy d.X d.Gz,_⁆ = conjugateSpanBy d.X d.Gz
      rw [hclosure]
      exact hcomm
    · rcases hrows with ⟨hP,hswap | ⟨hTK,hlin | hsym | hexc⟩⟩ | ⟨_,hP,hTK,hHeld⟩
      · exact ⟨hP,Or.inl hswap⟩
      · exact ⟨hP,Or.inr ⟨hTK,Or.inl hlin⟩⟩
      · exact (hnc hsym.2).elim
      · exact ⟨hP,Or.inr ⟨hTK,Or.inr (Or.inl hexc.2)⟩⟩
      · exact ⟨hP,Or.inr ⟨hTK,Or.inr (Or.inr hHeld)⟩⟩

/-- Frattini factorization for the literal section centralizer and its
original Sylow subgroup S=O₂(XT). -/
theorem quiet_point_sectionCentralizer_factor {z : G}
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let N := d.Gz ⊓ normalizer (d.X : Set G)
    let Y := commutatorPreimage N d.X (d.X.pCoreIn 2)
    Y ⊔ (N ⊓ normalizer (d.S : Set G)) = N := by
  dsimp only
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let N := d.Gz ⊓ normalizer (d.X : Set G)
  let Y := commutatorPreimage N d.X (d.X.pCoreIn 2)
  have hncore : N ≤ normalizer (d.X.pCoreIn 2 : Set G) :=
    inf_le_right.trans (normalizer_le_normalizer_characteristic_image d.X (pCore 2 d.X))
  have hNY : N ≤ normalizer (Y : Set G) :=
    commutatorPreimage_normalized N d.X (d.X.pCoreIn 2) N hncore
      N.le_normalizer inf_le_right hncore
  obtain ⟨R,hR⟩ := quiet_point_sectionCentralizer_sylow (T := T) (L := L) hzT
  have hf := relative_sylow_frattini Y N (commutatorPreimage_le _ _ _) hNY R
  rwa [hR] at hf

/-- The radical-normalizer bound puts the normalizer supplement inside M. -/
theorem quiet_tensor_point_normalizer_factor
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let N := d.Gz ⊓ normalizer (d.X : Set G)
    let Y := commutatorPreimage N d.X (d.X.pCoreIn 2)
    N = Y ⊔ (N ⊓ D.maximalLocal) := by
  dsimp only
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let N := d.Gz ⊓ normalizer (d.X : Set G)
  let Y := commutatorPreimage N d.X (d.X.pCoreIn 2)
  apply le_antisymm
  · conv_lhs => rw [←quiet_point_sectionCentralizer_factor (T := T) (L := L) hzT]
    exact sup_le_sup_left (inf_le_inf_left N
      (quiet_tensor_point_radical_normalizer_le D hJ e hbase hzV hzT)) Y
  · exact sup_le (commutatorPreimage_le _ _ _) inf_le_left


/-- The exact relative product N_{G_z}(X)=Y_z N_M(X), with the second
factor also restricted to G_z. -/
theorem quiet_tensor_point_normalizer_product
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let N := d.Gz ⊓ normalizer (d.X : Set G)
    let Y := commutatorPreimage N d.X (d.X.pCoreIn 2)
    (N : Set G) = (Y : Set G) * (N ⊓ D.maximalLocal : Subgroup G) := by
  dsimp only
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let N := d.Gz ⊓ normalizer (d.X : Set G)
  let Y := commutatorPreimage N d.X (d.X.pCoreIn 2)
  have hncore : N ≤ normalizer (d.X.pCoreIn 2 : Set G) :=
    inf_le_right.trans (normalizer_le_normalizer_characteristic_image d.X (pCore 2 d.X))
  have hNY : N ≤ normalizer (Y : Set G) :=
    commutatorPreimage_normalized N d.X (d.X.pCoreIn 2) N hncore
      N.le_normalizer inf_le_right hncore
  rw [←coe_mul_of_right_le_normalizer_left Y _ (inf_le_left.trans hNY)]
  exact congrArg (fun A : Subgroup G => (A : Set G))
    (quiet_tensor_point_normalizer_factor D hJ e hbase hzV hzT)

/-- The solvable section-centralizer subcase of 8.3.7 controls all of
N_{G_z}(X), using the original S and its weak-closure containment. -/
theorem quiet_tensor_solvable_point_normalizer_le
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let N := d.Gz ⊓ normalizer (d.X : Set G)
    let Y := commutatorPreimage N d.X (d.X.pCoreIn 2)
    Group.IsSolvable Y → N ≤ D.maximalLocal := by
  dsimp only
  intro hsolv
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let N := d.Gz ⊓ normalizer (d.X : Set G)
  let Y := commutatorPreimage N d.X (d.X.pCoreIn 2)
  let := hsolv
  have hYM : Y ≤ D.maximalLocal :=
    quiet_tensor_solvable_overgroup_le D hn e hbase hzV hz1 hzT Y
      (quiet_point_sectionCentralizer_sylow hzT)
  rw [quiet_tensor_point_normalizer_factor D hJ e hbase hzV hzT]
  exact sup_le hYM inf_le_right

/-- When X is normal in G_z, the source Frattini product is G_z=Y_z M_z.
No solvability of Y_z is assumed for this factorization. -/
theorem quiet_tensor_normal_point_factor
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    (d.X.subgroupOf d.Gz).Normal →
      (d.Gz : Set G) = (commutatorPreimage d.Gz d.X (d.X.pCoreIn 2) : Set G) *
        (d.Mz : Set G) := by
  dsimp only
  intro hnormal
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have he : d.Gz ⊓ normalizer (d.X : Set G) = d.Gz :=
    inf_of_le_left ((normal_subgroupOf_iff_le_normalizer
      (d.X_le.trans inf_le_right)).mp hnormal)
  have hf := quiet_tensor_point_normalizer_product D hJ e hbase hzV hzT
  change ((d.Gz ⊓ normalizer (d.X : Set G) : Subgroup G) : Set G) = _ at hf
  rw [he] at hf
  simpa only [d,CentralizerSetup.Mz,CentralizerSetup.M,FundamentalSetup.maximalLocal,
    inf_comm] using hf

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
