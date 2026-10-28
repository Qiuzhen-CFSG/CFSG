module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.SingleFactor
public import Theory.Representation.BinaryPermutation.SixCoreResidualMovement

/-!
# The original residual two-core moves its three-space

The five-dimensional CoreMarking constructs a surjection from the literal
C_L(z) onto the stabilizer of its marked vector. Its kernel is exactly
the restriction of O₂,Z(L), and its action uses the original conjugation.
When that kernel is a two-group, residual and two-core transport lift the
six-letter movement witness to [[V,L₁],O₂(L₁)] ≠ 1, with the original
L₁ = O^{3′}(C_L(z)). No split extension of L is assumed.

BlockAction applies this nontrivial commutator to the source centralizer
module. The other A₆-block steps remain with qt-d-1341-solvable-source.
Source: Aschbacher–Smith 13.4.8, printed p.904, the calculation of V₃
and its nontrivial commutator with O₂(L₁).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Chapter12.Section02 BinaryNaturalDual.VectorStabilizers Stellmacher
open Chapter14.Section03.FaithfulSource Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The literal component centralizer acts onto the marked vector stabilizer. -/
theorem component_centralizer_action (D : ChosenModule T L V) (m : CoreMarking D) (z : V) :
    ∃ f : (L ⊓ centralizer ({z.val} : Set G) : Subgroup G) →*
      BinaryPermutation.SixCoreStabilizer.stabilizer (m.coordinate z).toAdd,
      Function.Surjective f ∧
      f.ker = (centralCore L).comap (inclusion inf_le_left) ∧
      ∀ (c : (L ⊓ centralizer ({z.val} : Set G) : Subgroup G)) (v : V),
        (m.coordinate (V.normalizerMonoidHom ⟨c.val,D.normalizes c.property.1⟩ v)).toAdd =
        BinaryPermutation.alternatingCoreRepresentation (Fin 6) (f c).val (m.coordinate v).toAdd := by
  let C := L ⊓ centralizer ({z.val} : Set G)
  let S := BinaryPermutation.SixCoreStabilizer.stabilizer (m.coordinate z).toAdd
  let q : L →* alternatingGroup (Fin 6) :=
    m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hq : Function.Surjective q :=
    m.quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  have heq (l : L) : q l ∈ S ↔ l.val ∈ centralizer ({z.val} : Set G) := by
    change BinaryPermutation.coreRepresentation (Fin 6)
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).val (m.coordinate z).toAdd =
        (m.coordinate z).toAdd ↔ _
    rw [← m.equivariant l z]
    rw [Multiplicative.toAdd.injective.eq_iff,m.coordinate.injective.eq_iff,Subtype.ext_iff]
    change l.val * z.val * l.val⁻¹ = z.val ↔ _
    rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff,eq_comm]
  let k : C →* L := inclusion inf_le_left
  let f : C →* S := (q.comp k).codRestrict S (fun c => (heq (k c)).mpr c.property.2)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨l,hl⟩ := hq a.val
    have hlC : l.val ∈ C := ⟨l.property,(heq l).mp (hl ▸ a.property)⟩
    exact ⟨⟨l.val,hlC⟩,Subtype.ext hl⟩
  have hk : f.ker = (centralCore L).comap k := by
    ext c
    change (⟨q (k c),_⟩ : S) = 1 ↔ k c ∈ centralCore L
    rw [Subtype.ext_iff]
    change m.quotient (QuotientGroup.mk' (centralCore L) (k c)) = 1 ↔ _
    rw [m.quotient.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  exact ⟨f,hf,hk,fun c v => m.equivariant (k c) v⟩

/-- In the original five-space, O₂(L₁) acts nontrivially on [V,L₁]. -/
theorem firstCentralizerResidual_double_commutator_ne_bot
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcore : IsPGroup 2 (centralCore L)) (z : V)
    (hz : z.val ∉ centralizer (L : Set G)) :
    (⁅⁅V,firstCentralizerResidual L z.val⁆,
      (firstCentralizerResidual L z.val).pCoreIn 2⁆ : Subgroup G) ≠ ⊥ := by
  let C := L ⊓ centralizer ({z.val} : Set G)
  let w := (m.coordinate z).toAdd
  let S := BinaryPermutation.SixCoreStabilizer.stabilizer w
  obtain ⟨f,hf,hk,he⟩ := component_centralizer_action D m z
  have hpk : IsPGroup 2 f.ker := by
    rw [hk]
    exact hcore.comap_of_injective _ (inclusion_injective _)
  have hfix : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a w = w := by
    intro h
    exact hz ((m.mem_fixed_iff z).mpr
      ((BinaryPermutation.core_fixed_iff_constant (by simp) w).mp h))
  obtain ⟨a,b,ha,hb,u,hm⟩ :=
    BinaryPermutation.SixCoreResidualMovement.exists_residual_core_movement w hfix
  have har : a ∈ (primeToResidual 3 C).map f := by
    rwa [map_primeToResidual_of_surjective 3 f hf]
  obtain ⟨a₀,ha₀,hea⟩ := har
  have hbr : b ∈ ((primeToResidual 3 C).pCoreIn 2).map f := by
    rwa [map_pCoreIn_of_ker_isPGroup f hpk,map_primeToResidual_of_surjective 3 f hf]
  obtain ⟨b₀,hb₀,heb⟩ := hbr
  have haL : a₀.val ∈ firstCentralizerResidual L z.val := by
    rw [firstCentralizerResidual_eq]
    exact mem_map_of_mem C.subtype ha₀
  have hbL : b₀.val ∈ (firstCentralizerResidual L z.val).pCoreIn 2 := by
    rw [firstCentralizerResidual_eq,← map_pCoreIn_of_injective 2 _ _ C.subtype_injective]
    exact mem_map_of_mem C.subtype hb₀
  let v := m.coordinate.symm (Multiplicative.ofAdd u)
  let x : V := V.normalizerMonoidHom ⟨a₀.val,D.normalizes a₀.property.1⟩ v * v⁻¹
  have hx : x.val ∈ (⁅V,firstCentralizerResidual L z.val⁆ : Subgroup G) := by
    rw [commutator_comm]
    exact commutator_mem_commutator haL v.property
  have hxcoord : (m.coordinate x).toAdd =
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a.val u - u := by
    change (m.coordinate (V.normalizerMonoidHom _ v * v⁻¹)).toAdd = _
    rw [map_mul,map_inv]
    rw [toAdd_mul,toAdd_inv,← sub_eq_add_neg]
    rw [he,hea]
    simp only [v,MulEquiv.apply_symm_apply,toAdd_ofAdd]
  intro hbot
  have hcomm : Commute x.val b₀.val :=
    commutatorElement_eq_one_iff_mul_comm.mp
      (show ⁅x.val,b₀.val⁆ = 1 from by
        have hh := commutator_mem_commutator hx hbL
        rwa [hbot,mem_bot] at hh)
  have hfixed : V.normalizerMonoidHom ⟨b₀.val,D.normalizes b₀.property.1⟩ x = x := by
    apply Subtype.ext
    change b₀.val * x.val * b₀.val⁻¹ = x.val
    rw [hcomm.symm.eq,mul_inv_cancel_right]
  have hh := he b₀ x
  rw [hfixed,heb,hxcoord] at hh
  exact hm hh.symm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
