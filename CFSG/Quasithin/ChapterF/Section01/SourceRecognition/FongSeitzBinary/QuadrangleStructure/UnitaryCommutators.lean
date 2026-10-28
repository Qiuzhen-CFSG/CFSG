module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryOppositeCommutator
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.ProfileActors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryCenterEquality

/-!
# Both U5 mixed commutators from the original source data

The actual original linear-actor quotient of DGS (11.8)(b) identifies the
full root-generated SL2 actor, including its original endpoint lifts.
The new degree argument proves that the two unitary roots cannot commute;
Cartan irreducibility gives their entire intervening linear root.
Independently, the original special beta radical in (11.8)(f) transports
its derived, center and Frattini equality through the same marked core
map. The inverse-norm action then proves the other mixed commutator is
exactly the intrinsic center of the crossed unitary root.

Both source commutator equalities now follow without assuming either
commutator, an original Sylow-elementarity premise, or a derived-order
premise. The actual original linear quotient, the faithful local unitary
marking, specialness and section 2/5 reflection/kernel containments remain
explicit earlier-source inputs. The arbitrary marking preserves both
endpoints and the full overlap and includes independent geometric marks;
the original specialization retains Q.q on every actor representative.
The two fields are only required to have the source cardinalities, and
both orientations and fixed-field orders two and four are included.

This proves the commutator part of Fong--Seitz I (6A)(c). Identification of
the full second actor with SU3, rather than its faithful projective image,
and the required U5 irreducible actions remain with this structural family.
The later compatible Hermitian realizations and the equations consumed by
UnitarySource.FiveApplication remain with the unitary-recognition owner.

Source: DGS (11.8)(a,b,f), pp.175--176;
Fong--Seitz I (3G), (4B), (5C), (6A)(c), pp.14--16,19--22,26,37.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- The original linear actor and special beta radical supply BOTH exact
mixed commutators, retaining the full linear actor and its actual original lifts. -/
theorem marked_unitary_commutators
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = (2^n)^2)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split i)
    (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
    (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf ((S ⊔ L i).subgroupOf (parabolic L S i)))
    (ν : localGroup Q split j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) :
    ∃ μ : rankOne Q split i ≃* SL(2,K),
      (∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        MarkedLocal.endpointMap Q e i a.val = r ∧ μ r = f a) ∧
      ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = rootAt Q split i (Q.simple j) ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype := by
  let : ((S ⊔ L i).subgroupOf (parabolic L S i)).Normal := marked_sylow_factor_normal Q e h split i
  obtain ⟨μ,ξ,_,hμ⟩ := marked_linear_localGroup Q e h split i s hVi _
    (subgroupOf_mono _ le_sup_left) f hf hk
  have hfirst := Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.unitary_opposite_commutator
    Q split J hn hK hE hfixed hJ hm i j hij hVi hVj s μ ν
  let a := markedCoreEquiv Q e h split j hVj
  have hd : _root_.commutator (simpleRemainder Q split j) = center (simpleRemainder Q split j) := by
    have he := congrArg (Subgroup.map a.toMonoidHom) hderived
    rwa [map_commutator_eq,MonoidHom.range_eq_top.mpr a.surjective,←_root_.commutator_def,
      center_map_equiv] at he
  have hp : frattini (simpleRemainder Q split j) = center (simpleRemainder Q split j) := by
    have he := congrArg (Subgroup.map a.toMonoidHom) hfrattini
    rwa [frattini_map_equiv,center_map_equiv] at he
  have hd' : ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ =
      (center (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype := by
    rw [←hd,map_subtype_commutator]
  have hab := simpleRoot_commutator_eq_bot_of_linear Q split i ξ
  have hsecond := Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.unitary_cross_root_commutator_eq_center
    Q split J hn hE hfixed hJ hm i j hij hVi hVj ν hab hd'.ge
  have hz := Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.remainder_center_eq_cross_center
    Q split hm i j hij hVi hVj hab hd'.ge
  refine ⟨μ,hμ,hfirst,hsecond,?_⟩
  rw [hp,hz]
  exact hsecond

include h in
omit Q e split in
/-- The original quotient application retains Q.q on every full linear actor
representative and proves both commutators in that SAME quotient. -/
theorem original_unitary_commutators
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = (2^n)^2)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q₀ = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
    (hVj : simpleRemainder Q₀ split₀ j ≤ localKernel Q₀ j)
    (s : RootReflection Q₀ split₀ i)
    (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
    (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf ((S ⊔ L i).subgroupOf (parabolic L S i)))
    (ν : localGroup Q₀ split₀ j ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) :
    ∃ μ : rankOne Q₀ split₀ i ≃* SL(2,K),
      (∀ r : rankOne Q₀ split₀ i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        Q₀.q ⟨a.val,parabolic_le_generated i a.val.property⟩ = r ∧ μ r = f a) ∧
      ⁅simpleRoot Q₀ split₀ j,rootAt Q₀ split₀ j (Q₀.simple i)⁆ = rootAt Q₀ split₀ i (Q₀.simple j) ∧
      ⁅simpleRoot Q₀ split₀ i,rootAt Q₀ split₀ i (Q₀.simple j)⁆ =
        (center (rootAt Q₀ split₀ j (Q₀.simple i))).map (rootAt Q₀ split₀ j (Q₀.simple i)).subtype ∧
      ⁅simpleRoot Q₀ split₀ i,rootAt Q₀ split₀ i (Q₀.simple j)⁆ =
        (frattini (simpleRemainder Q₀ split₀ j)).map (simpleRemainder Q₀ split₀ j).subtype := by
  obtain ⟨μ,hμ,hfirst,hsecond,hphi⟩ := marked_unitary_commutators Q₀ (originalMarkedIso Q₀) h split₀
    J hn hK hE hfixed hJ hm i j hij hVi hVj s f hf hk ν hderived hfrattini
  refine ⟨μ,?_,hfirst,hsecond,hphi⟩
  intro r
  obtain ⟨a,ha,he⟩ := hμ r
  exact ⟨a,(original_endpointMap_apply Q₀ i a.val).symm.trans ha,he⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
