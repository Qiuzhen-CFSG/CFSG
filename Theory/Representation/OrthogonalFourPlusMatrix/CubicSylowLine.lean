module
public import Theory.Representation.OrthogonalFourPlusMatrix.SylowSingularLine
public import Theory.Representation.OrthogonalFourPlusMatrix.HyperplaneFixedMatrix
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Theory.GroupTheory.Commutator.FixedPointFree
public import Theory.Representation.BinaryConjugationSection.CommutatorImage

/-!
# Cubic displacement through the tensor Sylow commutator

A cubic fixing the full fixed line of a Sylow two-subgroup in the binary
four-dimensional tensor model has displacement contained in the movement
of its commutator with that Sylow. At the standard Sylow, fixing the singular
line forces inverse diagonal characters on the two factors. A nonidentity
cubic therefore acts without fixed points on both root groups, while its
tensor displacement has zero coordinate on the opposite line. The polar
form and explicit root displacements establish the claimed containment;
Sylow conjugacy transports it to the original Sylow subgroup.

Source: the field-four tensor geometry of Aschbacher--Smith 9.1.2 and
9.2.7, printed pp.729,731--732, in the Sylow-commutator form used by the
original PSL₃(4) residual application.
-/

public section
open Matrix Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open ClassicalOrthogonal.FourPlusMatrix ClassicalOrthogonal.FourPlusMatrix.Binary
attribute [local irreducible] Binary.action Binary.linearAction

private theorem point_fixer_entries (b : G)
    (hfix : action b (pointMap 1) = pointMap 1) :
    b.1.val 1 0 = 0 ∧ b.2.val 1 0 = 0 ∧ b.1.val 0 0 = b.2.val 1 1 := by
  have h := (Displacement.fixed_iff_intertwines _ _).mp hfix
  have h00 := congrArg (fun w : V => w 0 0) h
  have h11 := congrArg (fun w : V => w 1 1) h
  have h01 := congrArg (fun w : V => w 0 1) h
  exact ⟨by simpa [pointMap, Matrix.mul_apply, Fin.sum_univ_two] using h11,
    by simpa [pointMap, Matrix.mul_apply, Fin.sum_univ_two] using h00.symm,
    by simpa [pointMap, Matrix.mul_apply, Fin.sum_univ_two] using h01⟩

private theorem upper_eq_of_entries (a : SpecialLinearGroup (Fin 2) F)
    (h10 : a.val 1 0 = 0) (h00 : a.val 0 0 = 1) :
    a = SpecialLinearGroup.transvection zero_ne_one (a.val 0 1) := by
  have h11 : a.val 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, h10, h00, mul_zero, sub_zero, one_mul] using a.property
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe,h10,h00,h11]

private theorem point_cubic_entries (b : G) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hfix : action b (pointMap 1) = pointMap 1) :
    b.1.val 1 0 = 0 ∧ b.2.val 1 0 = 0 ∧
      b.1.val 0 0 ≠ 1 ∧ b.2.val 0 0 ≠ 1 := by
  obtain ⟨ha,hc,he⟩ := point_fixer_entries b hfix
  have hd : b.2.val 0 0 * b.2.val 1 1 = 1 := by
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using b.2.property
  have hne : b.1.val 0 0 ≠ 1 := by
    intro h1
    have h2 : b.2.val 0 0 = 1 := by simpa [←he,h1] using hd
    have hb2 : b ^ 2 = 1 := by
      apply Prod.ext
      · change b.1 ^ 2 = 1
        rw [upper_eq_of_entries b.1 ha h1, pow_two,
          ←SpecialLinearGroup.transvection_add]
        simp only [CharTwo.add_self_eq_zero,SpecialLinearGroup.transvection_coeff_zero]
      · change b.2 ^ 2 = 1
        rw [upper_eq_of_entries b.2 hc h2, pow_two,
          ←SpecialLinearGroup.transvection_add]
        simp only [CharTwo.add_self_eq_zero,SpecialLinearGroup.transvection_coeff_zero]
    apply hb1
    have hh := hb3
    rw [show (3 : ℕ) = 2+1 from rfl,pow_succ,hb2,one_mul] at hh
    exact hh
  refine ⟨ha,hc,hne,?_⟩
  intro h2
  apply hne
  simpa [h2,←he] using hd

private theorem upper_fixed_eq_one (a : SpecialLinearGroup (Fin 2) F)
    (ha : a.val 1 0 = 0) (hne : a.val 0 0 ≠ 1)
    (u : SpecialLinearGroup (Fin 2) F) (hu : u ∈ SpecialLinearGroup.upperUnipotent F)
    (hc : Commute a u) : u = 1 := by
  obtain ⟨x,rfl⟩ := (SpecialLinearGroup.mem_upperUnipotent F u).mp hu
  have he : a * SpecialLinearGroup.transvection zero_ne_one x * a⁻¹ =
      SpecialLinearGroup.transvection zero_ne_one x := by rw [hc.eq,mul_inv_cancel_right]
  rw [SpecialLinearGroup.triangular_conj_upper ha] at he
  have hx : a.val 0 0 ^ 2 * x = x := by
    simpa [SpecialLinearGroup.transvection_coe] using
      congrArg (fun w : SpecialLinearGroup (Fin 2) F => w.val 0 1) he
  have hs : a.val 0 0 ^ 2 ≠ 1 := fun hh => hne (CharTwo.sq_injective (by simpa using hh))
  have hz : x = 0 := (mul_eq_zero.mp
    (show (a.val 0 0 ^ 2 - 1) * x = 0 by rw [sub_mul,hx,one_mul,sub_self])).resolve_left
      (sub_ne_zero.mpr hs)
  simp [hz]

private theorem upperPair_cubic_commutator (b : G) (hb3 : b^3 = 1) (hb1 : b ≠ 1)
    (hfix : action b (pointMap 1) = pointMap 1) :
    ⁅(upperPairSylow : Subgroup G), zpowers b⁆ = (upperPairSylow : Subgroup G) := by
  obtain ⟨ha,hc,hne,hne'⟩ := point_cubic_entries b hb3 hb1 hfix
  have hn : b ∈ normalizer (upperPairSylow : Set G) := by
    apply mem_normalizer_iff.mpr
    intro u
    change u.1 ∈ SpecialLinearGroup.upperUnipotent F ∧
        u.2 ∈ SpecialLinearGroup.upperUnipotent F ↔ _
    exact and_congr (mem_normalizer_iff.mp ((SpecialLinearGroup.mem_rankOneBorel_iff _).mpr ha) u.1)
      (mem_normalizer_iff.mp ((SpecialLinearGroup.mem_rankOneBorel_iff _).mpr hc) u.2)
  apply Theory.GroupTheory.commutator_eq_of_fixedPointFree _ _ (zpowers_le.mpr hn) b
    (mem_zpowers b)
  intro u hu he
  apply Prod.ext
  · exact upper_fixed_eq_one b.1 ha hne u.1 hu.1
      (show Commute b.1 u.1 from congrArg Prod.fst he.eq)
  · exact upper_fixed_eq_one b.2 hc hne' u.2 hu.2
      (show Commute b.2 u.2 from congrArg Prod.snd he.eq)

private theorem upperPair_displacement_contains {w : V} (hw : w 1 0 = 0) :
    w ∈ subspaceCommutator action ⊤ (upperPairSylow : Subgroup G) := by
  let u : SpecialLinearGroup (Fin 2) F := SpecialLinearGroup.transvection zero_ne_one (1 : F)
  have hu : u ∈ SpecialLinearGroup.upperUnipotent F := ⟨Multiplicative.ofAdd 1,rfl⟩
  have h₁ : action (u,1) !![0,0;w 0 0,w 0 1] - !![0,0;w 0 0,w 0 1] ∈
      subspaceCommutator action ⊤ (upperPairSylow : Subgroup G) :=
    Submodule.subset_span ⟨(u,1),⟨hu,one_mem _⟩,_,Submodule.mem_top,rfl⟩
  have h₂ : action (1,u) !![0,0;w 1 1,0] - !![0,0;w 1 1,0] ∈
      subspaceCommutator action ⊤ (upperPairSylow : Subgroup G) :=
    Submodule.subset_span ⟨(1,u),⟨one_mem _,hu⟩,_,Submodule.mem_top,rfl⟩
  convert (subspaceCommutator action ⊤ (upperPairSylow : Subgroup G)).add_mem h₁ h₂ using 1
  apply Matrix.ext
  intro i j
  simp only [action_apply,u,inv_one,SpecialLinearGroup.coe_one,
    mul_one,one_mul,SpecialLinearGroup.transvection_inv,CharTwo.neg_eq,
    SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two,
    Matrix.sub_apply,Matrix.add_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply,hw]

private theorem upperPair_cubic_displacement (b : G) (hfix : action b (pointMap 1) = pointMap 1)
    (v : V) : action b v - v ∈ subspaceCommutator action ⊤ (upperPairSylow : Subgroup G) := by
  apply upperPair_displacement_contains
  have hp := HyperplaneFixedAux.polar_action b (pointMap 1) v
  have hact (x : V) : matrixAction b x = action b x := by rw [action_apply]; rfl
  simp only [hact] at hp
  rw [hfix] at hp
  have he : (action b v) 1 0 = v 1 0 := by
    rw [HyperplaneFixedAux.polar_formula,HyperplaneFixedAux.polar_formula] at hp
    change 0 * (action b v) 1 1 + 0 * (action b v) 0 0 +
        1 * (action b v) 1 0 + 0 * (action b v) 0 1 =
        0 * v 1 1 + 0 * v 0 0 + 1 * v 1 0 + 0 * v 0 1 at hp
    simpa only [zero_mul,one_mul,zero_add,add_zero] using hp
  simpa using sub_eq_zero.mpr he

private theorem action_mul_apply (a b : G) (v : V) :
    action (a*b) v = action a (action b v) :=
  congrArg (fun f : Module.End (ZMod 2) V => f v) (action.map_mul a b)

private theorem moved_conjugate (P Q : Subgroup G) (g : G)
    (hPQ : P.map (MulAut.conj g).toMonoidHom = Q) :
    subspaceCommutator action ⊤ P ≤ (subspaceCommutator action ⊤ Q).comap (action g) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p,hp,v,_,rfl⟩
  change action g (action p v-v) ∈ subspaceCommutator action ⊤ Q
  have hpg : g*p*g⁻¹ ∈ Q := hPQ ▸ mem_map_of_mem _ hp
  have he : action g (action p v-v) = action (g*p*g⁻¹) (action g v) - action g v := by
    rw [map_sub]
    apply congrArg (fun z : V => z - action g v)
    conv_rhs => rw [←action_mul_apply,inv_mul_cancel_right,action_mul_apply]
  rw [he]
  exact Submodule.subset_span ⟨_,hpg,_,Submodule.mem_top,rfl⟩

/-- A cubic fixing the tensor Sylow line moves only through its commutators with that Sylow group. -/
theorem sylow_line_cubic_displacement (P : Sylow 2 G) (b : G) (hb3 : b^3=1)
    (hfix : ∀ w ∈ fixedSpace action (P : Subgroup G), action b w = w) (v : V) :
    action b v-v ∈ subspaceCommutator action ⊤ ⁅(P : Subgroup G),zpowers b⁆ := by
  by_cases hb1 : b=1
  · subst b
    simp
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G upperPairSylow P
  have hPmap : (upperPairSylow : Subgroup G).map (MulAut.conj g).toMonoidHom =
      (P : Subgroup G) := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul] at hh
    exact hh
  let b' := g⁻¹*b*g
  have hb'3 : b'^3=1 := by
    have he : b' = MulAut.conj g⁻¹ b := by simp [b']
    rw [he,←map_pow,hb3,map_one]
  have hb'1 : b'≠1 := by
    intro he
    apply hb1
    apply (MulAut.conj g⁻¹).map_eq_one_iff.mp
    simpa [b'] using he
  have hbg (w : V) : action g (action b' w) = action b (action g w) := by
    have hh : g*b'=b*g := by dsimp [b']; group
    rw [←action_mul_apply,hh,action_mul_apply]
  have hp : action g (pointMap 1) ∈ fixedSpace action (P : Subgroup G) := by
    intro a
    obtain ⟨u,hu,he⟩ := hPmap.ge a.property
    change g*u*g⁻¹=a.val at he
    have huf := fixedSpace_upperPair.ge (show pointMap 1 ∈ point from ⟨1,rfl⟩) ⟨u,hu⟩
    change action u (pointMap 1) = pointMap 1 at huf
    change action a.val (action g (pointMap 1)) = _
    rw [←he,←action_mul_apply,inv_mul_cancel_right,action_mul_apply,huf]
  have hf : action b' (pointMap 1) = pointMap 1 := by
    apply (linearAction g).injective
    simp only [linearAction_apply]
    exact (hbg _).trans (hfix _ hp)
  have hc : ⁅(P : Subgroup G),zpowers b⁆ = (P : Subgroup G) := by
    have hh := congrArg (fun U : Subgroup G => U.map (MulAut.conj g).toMonoidHom)
      (upperPair_cubic_commutator b' hb'3 hb'1 hf)
    rw [map_commutator,hPmap,MonoidHom.map_zpowers] at hh
    have hbb : (MulAut.conj g).toMonoidHom b'=b := by dsimp [b']; group
    rwa [hbb] at hh
  rw [hc]
  have hm := moved_conjugate _ _ g hPmap
    (upperPair_cubic_displacement b' hf (action g⁻¹ v))
  rw [Submodule.mem_comap] at hm
  have hcancel : action g (action g⁻¹ v)=v := by
    rw [←action_mul_apply,mul_inv_cancel,action.map_one]
    rfl
  rwa [map_sub,hbg,hcancel] at hm

end ClassicalOrthogonal.FourPlusMatrix.Binary
