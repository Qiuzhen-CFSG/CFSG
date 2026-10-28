module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.LinearActions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.Conventions
public import Theory.Frattini.PGroup
public import Theory.Representation.PSL3Two.ResidualFFForms

/-!
# The actual actor and its binary radius displacement

The source actor lies in the adjacent kernel, hence in the vertex stabilizer.
Its intrinsic Frattini condition makes its image under the marked projection
onto SL₃(2) elementary abelian. The image order is exactly the prescribed
relative index, and the radius displacement is exactly the fixed codimension
of conjugation on the literal V/Z quotient. No triviality of the kernel's
action or elementary abelianness of the original actor is asserted.

These are the actor and numerical inputs to the binary obstruction in
Meierfrankenfeld--Stellmacher (1993), (4.6.2), printed p.901. The vanishing of
commutator forms, and hence the source obstruction, remain separate arguments.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial

universe u

variable {M : Type u} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem elementary_of_square_one {T : Type*} [Group T]
    (h : ∀ x : T, x ^ 2 = 1) : IsElementaryAbelian 2 T := by
  have hi (x : T) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h x)
  let : IsMulCommutative T := ⟨⟨fun x y => by
    have he := mul_inv_rev x y
    simpa only [hi] using he⟩⟩
  exact ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr h⟩

/-- The linear action is conjugation on the literal radius quotient by Z. -/
noncomputable def radiusRepresentation [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false) :
    letI := radiusZ_normal common a ha
    letI := radiusQuotient_elementary common hb a ha
    Representation (ZMod 2) (stabilizer R a)
      (Additive ((V R a) ⧸ (Z R a).subgroupOf (V R a))) := by
  let := radiusZ_normal common a ha
  let := radiusQuotient_elementary common hb a ha
  exact Offenders.linearize (radiusQuotientAction common a ha)

/-- Passing to binary coordinates does not change the actual quotient action. -/
theorem radiusRepresentation_apply [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false) (g : stabilizer R a) :
    letI := radiusZ_normal common a ha
    letI := radiusQuotient_elementary common hb a ha
    ∀ v : Additive ((V R a) ⧸ (Z R a).subgroupOf (V R a)),
      radiusRepresentation common hb a ha g v =
        Additive.ofMul (radiusQuotientAction common a ha g v.toMul) := by
  intros
  rfl

private theorem fixedSpace_subgroup_index {G T : Type*} [Group G] [Group T]
    [IsElementaryAbelian 2 T] [Finite T] (action : G →* MulAut T) (A : Subgroup G) :
    (Subgroup.toAddSubgroup.symm
      (fixedSpace (Offenders.linearize action) A).toAddSubgroup).index =
      2 ^ fixedCodim (Offenders.linearize action) A := by
  let ρ := Offenders.linearize action
  let C := Subgroup.toAddSubgroup.symm (fixedSpace ρ A).toAddSubgroup
  let e : fixedSpace ρ A ≃ C := {
    toFun := fun v => ⟨v.val.toMul, v.property⟩
    invFun := fun x => ⟨Additive.ofMul x.val, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hC : Nat.card C = 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ A) := by
    have hf := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A)
    rw [Nat.card_zmod] at hf
    exact (Nat.card_congr e).symm.trans hf
  have hT : Nat.card T = 2 ^ Module.finrank (ZMod 2) (Additive T) :=
    (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive T)).trans (by rw [Nat.card_zmod])
  have hdim := fixedCodim_add_finrank ρ A
  have hmul := C.card_mul_index
  rw [hC, hT, ← hdim, pow_add, Nat.mul_comm (2 ^ fixedCodim ρ A)] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul

/-- The exact source displacement, not a bound obtained by truncating the actor. -/
theorem radius_fixedCodim_pow [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ stabilizer R a) :
    letI := radiusZ_normal common a ha
    letI := radiusQuotient_elementary common hb a ha
    2 ^ fixedCodim (radiusRepresentation common hb a ha)
        (A.subgroupOf (stabilizer R a)) = (radiusFixed geometry a A).relIndex (V R a) := by
  let := radiusZ_normal common a ha
  let := radiusQuotient_elementary common hb a ha
  let := finite_radius common a ha
  rw [radiusFixed_relIndex_eq common a ha A hA]
  have hfix : radiusQuotientFixed common a ha A = Subgroup.toAddSubgroup.symm
      (fixedSpace (radiusRepresentation common hb a ha)
        (A.subgroupOf (stabilizer R a))).toAddSubgroup := by
    ext q
    rfl
  rw [hfix]
  exact (fixedSpace_subgroup_index (radiusQuotientAction common a ha)
    (A.subgroupOf (stabilizer R a))).symm

/-- The adjacent kernel contains the whole source actor inside the stabilizer. -/
theorem radius_actor_le_stabilizer [Finite M]
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R b) : A ≤ stabilizer R a := by
  have hb : color R b = true := by
    have hn := adjacent_color_ne R hab
    cases hc : color R b <;> simp_all
  exact hA.trans ((Q_h_eq_edge R hb hab).le.trans inf_le_left)

/-- The Frattini premise supplies precisely elementary abelianness of the
projected actor; the actor itself may be a nonabelian two-group. -/
theorem radius_projected_actor [Finite M]
    (source : LocalSource L R) (a b : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R b) (hnot : ¬ A ≤ Q R a)
    (hPhi : (frattini A).map A.subtype ≤ Q R a) :
    ∃ π : stabilizer R a →* SL, Function.Surjective π ∧
      π.ker = (Q R a).subgroupOf (stabilizer R a) ∧
      IsPGroup 2 π.ker ∧
      IsElementaryAbelian 2 ((A.subgroupOf (stabilizer R a)).map π) ∧
      (A.subgroupOf (stabilizer R a)).map π ≠ ⊥ ∧
      Nat.card ((A.subgroupOf (stabilizer R a)).map π) = (Q R a).relIndex A := by
  obtain ⟨frame⟩ := ModuleAlternatives.SourceCalculation.exists_frame a ha
  let π := frame.projection source
  have hAS := radius_actor_le_stabilizer a b ha hab A hA
  let := finite_stabilizer R a
  let : Finite A := Finite.of_injective (inclusion hAS) (inclusion_injective hAS)
  let : Fact (IsPGroup 2 A) := ⟨(ModuleAlternatives.kernel_isPGroup source b).to_le hA⟩
  have hker : π.ker = (Q R a).subgroupOf (stabilizer R a) := frame.projection_kernel source
  refine ⟨π, frame.projection_surjective source, hker, ?_, ?_, ?_, ?_⟩
  · rw [hker]
    exact (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype
  · apply elementary_of_square_one
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := hx
    apply Subtype.ext
    change π y ^ 2 = 1
    rw [← map_pow]
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact hPhi (mem_map_of_mem A.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨y, hy⟩ : A)))
  · intro he
    have hh := (Subgroup.map_eq_bot_iff _).mp he
    rw [hker] at hh
    exact hnot (fun x hx => hh (show (⟨x, hAS hx⟩ : stabilizer R a) ∈
      A.subgroupOf (stabilizer R a) from hx))
  · rw [← relIndex_ker, hker, subgroupOf, relIndex_comap,
      map_subgroupOf_eq_of_le hAS]

/-- The exact hypotheses of the source obstruction give a constituent budget
for the actual nonsplit radius representation and actual projected actor. -/
theorem radius_projected_offender [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R b) (hnot : ¬ A ≤ Q R a)
    (hPhi : (frattini A).map A.subtype ≤ Q R a)
    (hsmall : (radiusFixed geometry a A).relIndex (V R a) ≤ (Q R a).relIndex A) :
    letI := radiusZ_normal common a ha
    letI := radiusQuotient_elementary common hb a ha
    ∃ π : stabilizer R a →* SL, Function.Surjective π ∧
      π.ker = (Q R a).subgroupOf (stabilizer R a) ∧ IsPGroup 2 π.ker ∧
      IsElementaryAbelian 2 ((A.subgroupOf (stabilizer R a)).map π) ∧
      (A.subgroupOf (stabilizer R a)).map π ≠ ⊥ ∧
      fixedCodim (radiusRepresentation common hb a ha) (A.subgroupOf (stabilizer R a)) ≤
        rank ((A.subgroupOf (stabilizer R a)).map π) := by
  let := radiusZ_normal common a ha
  let := radiusQuotient_elementary common hb a ha
  obtain ⟨π, hπ, hker, hp, helem, hne, hcard⟩ :=
    radius_projected_actor source a b ha hab A hA hnot hPhi
  let := helem
  have hAI : IsElementaryTwo ((A.subgroupOf (stabilizer R a)).map π) := ⟨hne, helem⟩
  refine ⟨π, hπ, hker, hp, helem, hne, ?_⟩
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [← hAI.card_eq_two_pow_rank, hcard,
    radius_fixedCodim_pow common hb a ha A (radius_actor_le_stabilizer a b ha hab A hA)]
  exact hsmall

/-- The numerical source assumptions supply the checked simple-constituent
criterion for this same actor. This is not a classification of the radius. -/
theorem radius_offender_budget [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R b) (hnot : ¬ A ≤ Q R a)
    (hPhi : (frattini A).map A.subtype ≤ Q R a)
    (hsmall : (radiusFixed geometry a A).relIndex (V R a) ≤ (Q R a).relIndex A) :
    letI := radiusZ_normal common a ha
    letI := radiusQuotient_elementary common hb a ha
    ∃ d : ℕ,
      BinaryLinearThree.ResidualFFForms.SimpleBudget.{u} (A.subgroupOf (stabilizer R a)) d ∧
      fixedCodim (radiusRepresentation common hb a ha) (A.subgroupOf (stabilizer R a)) ≤ d := by
  let := radiusZ_normal common a ha
  let := radiusQuotient_elementary common hb a ha
  let := finite_stabilizer R a
  obtain ⟨π, hπ, _, hp, helem, hne, hcost⟩ :=
    radius_projected_offender common hb a b ha hab A hA hnot hPhi hsmall
  refine ⟨rank ((A.subgroupOf (stabilizer R a)).map π), ?_, hcost⟩
  exact BinaryLinearThree.ResidualFFForms.simpleBudget_of_surjective π hπ hp _ _
    (BinaryLinearThree.ResidualFFForms.simpleBudget _ hne helem)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
