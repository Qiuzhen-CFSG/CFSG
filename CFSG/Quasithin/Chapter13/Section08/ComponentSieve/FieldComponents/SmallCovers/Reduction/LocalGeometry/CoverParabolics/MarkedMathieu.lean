module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MarkedSetup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.NativeWitness
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MarkedMathieu.NativePlacement
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MarkedMathieu.ResidualTransport


/-!
# The marked Mathieu replacement

From the source's proper-residual setup and an actual M₂₂ quotient,
choose the native hexad containing the image of K ∩ M. Its full design
normalizer places the actual T in the same hexad. The order-three theta
generators belong to the canonical solvable residual K₁ because the
remaining quotient of the lift is a two-group.

The overlap K ∩ M is solvable, whereas K₁ has an A₆ quotient, so K₁ is
not contained in M. Its cover residual lies in the original Y < L₁.
These facts construct the complete replacement setup on K₁T, including
relative normality, the actual Sylow subgroup, the restricted theta
identity, the genuine triple-cover quotient, and the proper overlap.
The actual LocalSix witness and its central quotient coordinates are
retained. No replacement containment or residual compatibility is assumed.

Source: Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973), the
reduction from the covered M₂₂ to the covered A₆ under Y < L₁.
The subsequent marked-six parabolic argument is a separate source step.
-/

@[expose] public section

open Subgroup Sporadic.Mathieu Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
namespace MarkedMathieu
variable {G : Type*} [Group G] [Finite G]
variable {H K L₁ T G₁ M : Subgroup G} (s : MarkedSetup H K L₁ T G₁ M)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
include s e

/-- The literal theta generators lie in the canonical component of the lift. -/
theorem seed_le_hexadResidual {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hX : nativeImage K (K ⊓ M) e ≤ MulAction.stabilizer M22 B) :
    L₁ ≤ hexadResidualIn K e B := by
  let := s.quasisimple
  let F := hexadLift K e B
  have hp := hexadLift_quotient_residual_isTwoGroup K e s.center_card hB
  have hr : pResidual 2 F ≤ solvableResidual F := sInf_le ⟨inferInstance, hp⟩
  have hL := seed_le_hexadLift s e hX
  rw [s.theta]
  apply (closure_le _).mpr
  intro x hx
  have hxL : x ∈ L₁ := s.theta.symm ▸ subset_closure hx
  let y : F := ⟨x, hL hxL⟩
  have hy : y ∈ pResidual 2 F := by
    apply mem_pResidual_of_orderOf_coprime
    rw [← orderOf_coe y]
    change Nat.Coprime 2 (orderOf x)
    rw [hx.2]
    decide
  exact mem_map.mpr ⟨y, hr hy, rfl⟩

/-- The actual overlap is solvable, since both its native image and the
central two-core kernel are solvable. -/
theorem component_overlap_solvable : Group.IsSolvable (K ⊓ M : Subgroup G) := by
  let f := mathieuProjection K e
  let X := nativeImage K (K ⊓ M) e
  let := native_overlap_solvable s e
  let : Group.IsSolvable (QuotientGroup.mk' (pCore 2 K)).ker := by
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 K) := pCore_isNilpotent
    infer_instance
  let : Group.IsSolvable (centralPreimage (pCore 2 K)) :=
    isSolvable_comap_of_solvable_ker (QuotientGroup.mk' (pCore 2 K)) (center _)
  let : Group.IsSolvable f.ker := by rw [mathieuProjection_ker]; infer_instance
  let : Group.IsSolvable (X.comap f) := isSolvable_comap_of_solvable_ker f X
  let j : (K ⊓ M : Subgroup G) →* X.comap f :=
    (inclusion (show K ⊓ M ≤ K from inf_le_left)).codRestrict _
      (fun x => mem_map.mpr ⟨⟨x.val, x.property.1⟩, x.property, rfl⟩)
  apply Group.isSolvable_of_isSolvable_injective (f := j)
  intro x y h
  exact Subtype.ext (congrArg (fun z : X.comap f => z.val.val) h)

/-- The component cannot lie in M: it has an A₆ quotient, whereas K∩M
is solvable. -/
theorem hexadResidual_not_le_M {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ¬ hexadResidualIn K e B ≤ M := by
  let := s.quasisimple
  intro hM
  let := component_overlap_solvable s e
  let R := hexadResidualIn K e B
  have hRJ : R ≤ K ⊓ M := le_inf (hexadResidualIn_le K e B) hM
  let : Group.IsSolvable R := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hRJ) (inclusion_injective hRJ)
  let : Group.IsSolvable (alternatingGroup (Fin 6)) :=
    Group.isSolvable_of_surjective (hexadResidualCoverProjection_spec K e s.center_card hB).1
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6)) inferInstance

omit s [Finite G] in
/-- Characteristicity of the solvable residual provides relative normality
in K₁T directly from normalization of the hexad lift. -/
theorem hexadResidual_normal {B : Finset (Fin 22)}
    (hn : T ≤ normalizer (hexadLift K e B : Set G)) :
    ((hexadResidualIn K e B).subgroupOf (hexadResidualIn K e B ⊔ T)).Normal := by
  have hT : T ≤ normalizer (hexadResidualIn K e B : Set G) :=
    hn.trans (normalizer_le_normalizer_characteristic_image
      (hexadLift K e B) (solvableResidual (hexadLift K e B)))
  exact normal_subgroupOf_of_le_normalizer
    (sup_le (hexadResidualIn K e B).le_normalizer hT)

/-- Reconstruct the complete marked source setup on the canonical hexad component. -/
theorem replacementSetup {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hX : nativeImage K (K ⊓ M) e ≤ MulAction.stabilizer M22 B)
    (hn : T ≤ normalizer (hexadLift K e B : Set G)) :
    MarkedSetup (hexadResidualIn K e B ⊔ T) (hexadResidualIn K e B) L₁ T G₁ M := by
  let := s.quasisimple
  let w := localSix_hexad H K T s.mem_Hz.1.1 s.component_le s.sylow e s.center_card hB hn
  have hL := seed_le_hexadResidual s e hB hX
  have hout := hexadResidual_not_le_M s e hB
  have hRH : hexadResidualIn K e B ⊔ T ≤ H := sup_le
    ((hexadResidualIn_le K e B).trans s.component_le)
    (Chapter1.isSylowIn_iff.mp s.sylow).2.1
  have hcover := hexadResidualIn_isTripleCoverSix K e s.center_card hB
  exact {
    mem_Hz := replacement_mem_Hz H K L₁ T G₁ M s.mem_Hz s.component_le w hL hout
    component_le := le_sup_left
    component := w.local_mem.2.1
    component_normal := hexadResidual_normal e hn
    sylow := s.sylow.restrict le_sup_right hRH
    sylow_le_M := s.sylow_le_M
    generated := rfl
    seed_le_component := hL
    seed_solvable := s.seed_solvable
    theta := s.theta_restrict _ (hL.trans le_sup_left) hRH
    proper_residual := lt_of_le_of_lt (hexadResidual_coverResidual_le K e s.center_card hB)
      s.proper_residual
    quasisimple := hcover.1
    center_card := hcover.2.1
    solvable_overgroups := s.solvable_overgroups }

/-- The marked Mathieu replacement, with the literal hexad, actual local
witness, genuine triple cover and proper new overlap. All additional
replacement inputs have been discharged. -/
theorem exists_marked_replacement :
    ∃ B ∈ m22Blocks,
      T ≤ normalizer (hexadLift K e B : Set G) ∧
      L₁ ≤ hexadResidualIn K e B ∧
      ¬ hexadResidualIn K e B ≤ M ∧
      coverResidualIn (hexadResidualIn K e B) < L₁ ∧
      ∃ w : LocalSix K T, w.subgroup = hexadResidualIn K e B ∧
        w.subgroup < K ∧
        SolvableExclusion.IsTripleCoverSix (w.subgroup ⧸ pCore 2 w.subgroup) ∧
        MarkedSetup (w.subgroup ⊔ T) w.subgroup L₁ T G₁ M ∧
        (w.subgroup ⊔ T) ⊓ M < w.subgroup ⊔ T := by
  let := s.quasisimple
  obtain ⟨B, hB, hX, _, _, _, hn⟩ := exists_native_hexad s e
  let w := localSix_hexad H K T s.mem_Hz.1.1 s.component_le s.sylow e s.center_card hB hn
  let s' := replacementSetup s e hB hX hn
  exact ⟨B, hB, hn, seed_le_hexadResidual s e hB hX,
    hexadResidual_not_le_M s e hB, s'.proper_residual,
    w, rfl, hexadResidualIn_lt K e hB,
    hexadResidualIn_isTripleCoverSix K e s.center_card hB,
    s', s'.overlap_proper⟩

end MarkedMathieu
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
