module

public import Theory.AtlasPort.LinearGroups.G2.LieSylowCenter
public import Mathlib.GroupTheory.Commutator.Basic
public import Theory.AtlasPort.LinearGroups.G2.LocalNormalizer

/-!
# Intrinsic root subgroups in a positive-root Sylow subgroup

In characteristic two the highest-root subgroup consists of the central
involutions, including the identity. The two-long-root subgroup consists of
the involutions in the second center. The latter characterization follows
from the six-root multiplication law and the square equation. These intrinsic
descriptions support the invariant-parabolic step in Aschbacher–Smith 2.3.9(7),
printed p.526. The coordinate laws come from the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open scoped commutatorElement
namespace Atlas.G2.SylowParabolicInvariance
variable {G H : Type*} [Group G] [Group H]

def CentralInvolution (R : Subgroup G) (x : G) : Prop :=
  x ∈ R ∧ x ^ 2 = 1 ∧ ∀ y ∈ R, Commute x y

def SecondCentralInvolution (R : Subgroup G) (x : G) : Prop :=
  x ∈ R ∧ x ^ 2 = 1 ∧ ∀ y ∈ R, ∀ z ∈ R, Commute ⁅x,y⁆ z

theorem centralInvolution_map_iff (f : G →* H) (hf : Function.Injective f)
    (R : Subgroup G) (x : G) :
    CentralInvolution (R.map f) (f x) ↔ CentralInvolution R x := by
  constructor
  · rintro ⟨hx,hs,hc⟩
    refine ⟨(Subgroup.mem_map_iff_mem hf).mp hx, ?_, ?_⟩
    · apply hf
      simpa only [map_pow, map_one] using hs
    · intro y hy
      apply hf
      simpa only [map_mul] using (hc (f y) (Subgroup.mem_map_of_mem f hy)).eq
  · rintro ⟨hx,hs,hc⟩
    refine ⟨Subgroup.mem_map_of_mem f hx, ?_, ?_⟩
    · rw [← map_pow, hs, map_one]
    · rintro _ ⟨y,hy,rfl⟩
      exact (hc y hy).map f

theorem secondCentralInvolution_map_iff (f : G →* H) (hf : Function.Injective f)
    (R : Subgroup G) (x : G) :
    SecondCentralInvolution (R.map f) (f x) ↔ SecondCentralInvolution R x := by
  constructor
  · rintro ⟨hx,hs,hc⟩
    refine ⟨(Subgroup.mem_map_iff_mem hf).mp hx, ?_, ?_⟩
    · apply hf
      simpa only [map_pow, map_one] using hs
    · intro y hy z hz
      apply hf
      simpa only [map_mul, map_commutatorElement] using
        (hc (f y) (Subgroup.mem_map_of_mem f hy) (f z) (Subgroup.mem_map_of_mem f hz)).eq
  · rintro ⟨hx,hs,hc⟩
    refine ⟨Subgroup.mem_map_of_mem f hx, ?_, ?_⟩
    · rw [← map_pow, hs, map_one]
    · rintro _ ⟨y,hy,rfl⟩ _ ⟨z,hz,rfl⟩
      simpa only [map_commutatorElement] using (hc y hy z hz).map f

theorem map_eq_of_centralInvolutions (R K : Subgroup G)
    (hK : ∀ x, x ∈ K ↔ CentralInvolution R x)
    (b : MulAut G) (hb : R.map b.toMonoidHom = R) : K.map b.toMonoidHom = K := by
  ext x
  obtain ⟨y,rfl⟩ := b.surjective x
  change b.toMonoidHom y ∈ K.map b.toMonoidHom ↔ b.toMonoidHom y ∈ K
  rw [Subgroup.mem_map_iff_mem b.injective, hK, hK]
  simpa only [hb] using (centralInvolution_map_iff b.toMonoidHom b.injective R y).symm

theorem map_eq_of_secondCentralInvolutions (R K : Subgroup G)
    (hK : ∀ x, x ∈ K ↔ SecondCentralInvolution R x)
    (b : MulAut G) (hb : R.map b.toMonoidHom = R) : K.map b.toMonoidHom = K := by
  ext x
  obtain ⟨y,rfl⟩ := b.surjective x
  change b.toMonoidHom y ∈ K.map b.toMonoidHom ↔ b.toMonoidHom y ∈ K
  rw [Subgroup.mem_map_iff_mem b.injective, hK, hK]
  simpa only [hb] using (secondCentralInvolution_map_iff b.toMonoidHom b.injective R y).symm
end Atlas.G2.SylowParabolicInvariance

open Atlas.G2.Explicit Atlas.G2.LieParabolicSetup
open scoped commutatorElement
namespace Atlas.G2.SylowParabolicInvariance
variable {F : Type*} [Field F] [CharP F 2]

theorem highestRoot_iff_centralInvolution (g : Model F) :
    g ∈ highestRoot ↔ CentralInvolution unipotent g := by
  constructor
  · rintro ⟨a,rfl⟩
    refine ⟨(fiveRootSubgroup_le_unipotent _ _) (rootA_mem_radical₁ a.toAdd), ?_, ?_⟩
    · change rootA a.toAdd ^ 2 = 1
      rw [pow_two, rootA_add, CharTwo.add_self_eq_zero, rootA_zero]
    · intro y hy
      rw [unipotent_eq_range] at hy
      obtain ⟨t,rfl⟩ := hy
      exact (unipotentProduct_commute_rootA t a.toAdd).symm
  · rintro ⟨hg,_,hc⟩
    rw [← unipotent_center]
    refine ⟨⟨g,hg⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (hc y.val y.prop).eq.symm

omit [CharP F 2] in
private theorem parameters_eq_mod_highestRoot (t u : Fin 6 → F)
    (h : ⁅unipotentProduct t, unipotentProduct u⁆ ∈ highestRoot) :
    ∀ j : Fin 6, j ≠ 0 → unipotentProductParameters t u j =
      unipotentProductParameters u t j := by
  obtain ⟨a,ha⟩ := h
  change rootA a.toAdd = ⁅unipotentProduct t, unipotentProduct u⁆ at ha
  have he : unipotentProduct t * unipotentProduct u =
      rootA a.toAdd * (unipotentProduct u * unipotentProduct t) := by
    rw [ha, commutatorElement_def]
    group
  have ha' : rootA a.toAdd = unipotentProduct ![a.toAdd,0,0,0,0,0] := by
    simp [unipotentProduct]
  rw [ha', unipotentProduct_mul, unipotentProduct_mul, unipotentProduct_mul] at he
  have he' := unipotentProduct_injective he
  intro j hj
  have hej := congrFun he' j
  fin_cases j
  · exact (hj rfl).elim
  all_goals simpa [unipotentProductParameters] using hej

private theorem secondCentral_parameters (t : Fin 6 → F)
    (h : SecondCentralInvolution unipotent (unipotentProduct t)) :
    t = ![t 0,t 1,0,0,0,0] := by
  have hcom (u : Fin 6 → F) : ⁅unipotentProduct t,unipotentProduct u⁆ ∈ highestRoot := by
    rw [← unipotent_center]
    have hm : ⁅unipotentProduct t,unipotentProduct u⁆ ∈ unipotent := by
      rw [commutatorElement_def]
      exact unipotent.mul_mem (unipotent.mul_mem
        (unipotent.mul_mem (unipotentProduct_mem _) (unipotentProduct_mem _))
          (unipotent.inv_mem (unipotentProduct_mem _)))
            (unipotent.inv_mem (unipotentProduct_mem _))
    refine ⟨⟨_,hm⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro z
    exact Subtype.ext (h.2.2 _ (unipotentProduct_mem u) z.val z.prop).eq.symm
  have hE := parameters_eq_mod_highestRoot t ![0,0,0,0,1,0] (hcom _) 3 (by decide)
  have h5 : t 5 = 0 := by
    simpa [unipotentProductParameters] using hE
  have hF := parameters_eq_mod_highestRoot t ![0,0,0,0,0,1] (hcom _) 3 (by decide)
  have h4 : t 4 = 0 := by
    simpa [unipotentProductParameters] using hF.symm
  have hF' := parameters_eq_mod_highestRoot t ![0,0,0,0,0,1] (hcom _) 1 (by decide)
  have hthree : (3 : F) = 1 := by linear_combination CharP.cast_eq_zero F 2
  have h23 : t 2 = t 3 := by
    simp [unipotentProductParameters,h4,h5,hthree] at hF'
    linear_combination hF'
  have hs : unipotentProductParameters t t = 0 := by
    apply unipotentProduct_injective
    rw [← unipotentProduct_mul, ← pow_two, h.2.1, unipotentProduct_zero]
  have hs0 := congrFun hs 0
  have hsq : t 3 * t 3 = 0 := by
    simp [unipotentProductParameters,h4,h5,h23,hthree] at hs0
    linear_combination hs0 - (CharP.cast_eq_zero F 2) * t 0
  have h3 := (mul_self_eq_zero.mp hsq)
  ext j
  fin_cases j <;> simp [h4,h5,h23,h3]

omit [CharP F 2] in
private theorem longRoot_commutator (t : Fin 6 → F) (a b : F) :
    ⁅unipotentProduct t,rootA a * rootB b⁆ = rootA (-b * t 4) := by
  change (unipotentProduct t * (rootA a * rootB b) * (unipotentProduct t)⁻¹) *
    (rootA a * rootB b)⁻¹ = _
  apply mul_inv_eq_of_eq_mul
  rw [unipotent_conjugate_longRoot, ← mul_assoc, rootA_add]
  congr 2
  ring

theorem longRootLocal_iff_secondCentralInvolution (g : Model F) :
    g ∈ longRootLocal ↔ SecondCentralInvolution unipotent g := by
  constructor
  · rintro ⟨a,rfl⟩
    refine ⟨longRootLocal_le_unipotent ⟨a,rfl⟩, ?_, ?_⟩
    · change (longRootHom a) ^ 2 = 1
      rw [← map_pow]
      have ha : a ^ 2 = 1 := by
        rw [pow_two]
        apply Multiplicative.toAdd.injective
        change a.toAdd + a.toAdd = 0
        exact CharTwo.add_self_eq_zero _
      rw [ha,map_one]
    · intro y hy z hz
      rw [unipotent_eq_range] at hy hz
      obtain ⟨t,rfl⟩ := hy
      obtain ⟨u,rfl⟩ := hz
      change Commute ⁅rootA a.toAdd.1 * rootB a.toAdd.2,unipotentProduct t⁆ _
      rw [← commutatorElement_inv, longRoot_commutator]
      exact (unipotentProduct_commute_rootA u _).symm.inv_left
  · intro h
    have hg := h.1
    rw [unipotent_eq_range] at hg
    obtain ⟨t,rfl⟩ := hg
    rw [secondCentral_parameters t h]
    refine ⟨Multiplicative.ofAdd (t 0,t 1), ?_⟩
    simp [longRootHom,unipotentProduct]
end Atlas.G2.SylowParabolicInvariance

end
