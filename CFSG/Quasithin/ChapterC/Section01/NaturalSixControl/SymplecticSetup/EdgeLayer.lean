module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.MovingLayer
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.PointFull
public import Theory.GroupTheory.Commutator.NormalClosureSupplement
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The native symplectic edge layer has index eight

The edge seed is Ω₁Z(R). Since M=L R and R centralizes this seed, the full
commutator of its normal closure is its L-commutator, namely W. Each conjugate
of the seed therefore belongs to W times the seed. This gives Zα=Uα Zβ
without asserting any splitting of the entire X-layer.

The seed meets W in C_W(R). Under the actual full point-core image this has
order two, while W has order sixteen. The product cardinality formula gives
[Zα:Zβ]=8, and conjugation transports it to every original-group edge. The
last theorem uses the literal characteristic replacement and its relabeler.

Source: MS93 (3.2), (3.6), printed pp.863–864,871.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
include s

theorem seedHull_eq_module_sup_seed (h : NativeCentralLayer s) :
    normalClosure (omegaCenter R : Set M) = W ⊔ omegaCenter R := by
  let H := normalClosure (omegaCenter R : Set M)
  have hHL : ⁅H,L⁆ = W := by
    apply (map_injective (embedM_injective R))
    have he := h.U_eq_module
    rw [U,SymplecticSeed.Z_eq_seedHull,Ltilde_alpha,s.residual,←map_commutator] at he
    exact he
  have hHS : ⁅H,(⊤ : Subgroup M)⁆ ≤ W := by
    rw [normalClosure_commutator_eq_of_centralizing_supplement
      (omegaCenter R) L R s.sup_eq_top (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2)]
    rw [←hHL]
    exact commutator_mono le_normalClosure le_rfl
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    obtain ⟨a,ha,hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g,rfl⟩ := isConj_iff.mp hax
    have hc : ⁅g,a⁆ ∈ W := by
      apply hHS
      rw [commutator_comm]
      exact commutator_mem_commutator (mem_top g) (subset_normalClosure ha)
    have he : g*a*g⁻¹ = ⁅g,a⁆*a := by simp [commutatorElement_def,mul_assoc]
    rw [he]
    exact mul_mem (mem_sup_left hc) (mem_sup_right ha)
  · apply sup_le _ le_normalClosure
    rw [←hHL]
    exact commutator_le_left H L

theorem Z_eq_moving_sup_edge (h : NativeCentralLayer s) :
    Z R (alpha R) = U R (alpha R) ⊔ Z R (beta R) := by
  rw [SymplecticSeed.Z_eq_seedHull,s.seedHull_eq_module_sup_seed h,Subgroup.map_sup,h.U_eq_module]
  congr 1
  rw [Z,if_neg (by exact Bool.noConfusion : color R (beta R) ≠ false),edgeOmega,Q_beta,
    omegaCenter_map _ _ (embedM_injective R)]

theorem module_inf_seed_eq_fixed : W ⊓ omegaCenter R = W ⊓ centralizer (R : Set M) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2)
  · intro w hw
    refine ⟨hw.1,mem_omegaCenter_iff.mpr ⟨s.core_le (s.module_le_core hw.1),?_,hw.2⟩⟩
    exact (mem_omegaCenter_iff.mp (s.module_le_ambientX hw.1)).2.1

theorem module_inf_seed_card (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom) :
    Nat.card (W ⊓ omegaCenter R : Subgroup M) = 2 := by
  let := s.module_elementary
  have hE : R.map s.projection = Model.E.map (MulAut.conj t).toMonoidHom := by
    rwa [Model.pointCore_eq_exceptional] at hfull
  let d : NaturalAction W := ⟨s.projection,
    s.projection_surjective_of_radical_image_le_conjugate t hE.le,
    s.projection_kernel,s.coordinates,s.action⟩
  rw [s.module_inf_seed_eq_fixed,d.fixed_card]
  have hd : Module.finrank (ZMod 2) (fixedSpace Model.rho (R.map d.q)) = 1 := by
    have hcodim : fixedCodim Model.rho (R.map s.projection) = 3 := by
      rw [hE,fixedCodim_map_conj]
      exact ChapterB.Offenders.Six.fixedCodim_exceptional.2.2.2
    have hdim := fixedCodim_add_finrank Model.rho (R.map s.projection)
    rw [hcodim,finrank_natural_even (Fin 6) (by decide)] at hdim
    change 3 + _ = 4 at hdim
    change Module.finrank (ZMod 2) (fixedSpace Model.rho (R.map s.projection)) = 1
    omega
  norm_num [hd]

theorem edge_Z_index_eight (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom) :
    (Z R (beta R)).relIndex (Z R (alpha R)) = 8 := by
  have hw : Nat.card W = 16 := by
    rw [Nat.card_congr s.coordinates.toEquiv]
    change Nat.card (natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      finrank_natural_even (Fin 6) (by decide)]
    rfl
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes W (omegaCenter R)
    (show omegaCenter R ≤ normalizer (W : Set M) from le_normalizer_of_normal)
  rw [hw,s.module_inf_seed_card t hfull,←s.seedHull_eq_module_sup_seed h] at hp
  have hi := relIndex_mul_relIndex (⊥ : Subgroup M) (omegaCenter R)
    (normalClosure (omegaCenter R : Set M)) bot_le le_normalClosure
  rw [relIndex_bot_left,relIndex_bot_left] at hi
  have hspos : 0 < Nat.card (omegaCenter R) := Nat.card_pos
  have hindex : (omegaCenter R).relIndex (normalClosure (omegaCenter R : Set M)) = 8 := by
    nlinarith
  have hseed : Z R (beta R) = (omegaCenter R).map (embedM R) := by
    rw [Z,if_neg (by exact Bool.noConfusion : color R (beta R) ≠ false),edgeOmega,Q_beta,
      omegaCenter_map _ _ (embedM_injective R)]
  rw [hseed,SymplecticSeed.Z_eq_seedHull,relIndex_map_map_of_injective _ _ (embedM_injective R)]
  exact hindex

theorem edge_Z_index_eight_at (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    {a b : Vertex R} (ha : color R a = false) (hab : Adjacent R a b) :
    (Z R b).relIndex (Z R a) = 8 := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R a b).mp hab
  · rcases hg with ⟨rfl,rfl⟩
    have he := relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (Z R (beta R)) (Z R (alpha R))
      (MulAut.conj g⁻¹).injective
    rw [←Z_act,←Z_act] at he
    simp only [alpha,beta,act_mVertex,act_hVertex,one_mul] at he
    exact he.trans (s.edge_Z_index_eight h t hfull)
  · rw [hg.1] at ha
    cases ha

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L V T)

theorem reducedSource_edge_Z_index_eight (h : IntrinsicMSPair d)
    (r : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hfull : r.radical.map ((originalSource d h).reduce r).projection =
      pointCore.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom)
    {a b : Vertex r.radical} (ha : color r.radical a = false)
    (hab : Adjacent r.radical a b) :
    (Z r.radical b).relIndex (Z r.radical a) = 8 :=
  Source.edge_Z_index_eight_at ((originalSource d h).reduce r)
    (reduced_nativeCentralLayer d h r) d.relabeler.val⁻¹ hfull ha hab

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
