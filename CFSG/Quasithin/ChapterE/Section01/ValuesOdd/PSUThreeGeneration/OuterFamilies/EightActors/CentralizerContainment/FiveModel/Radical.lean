module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.ActorImage
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.PrimeReduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.FiveModel.Radical.InnerModel
public import Theory.SpecificGroups.SU3.FiveCentralizerRadical.Outer

/-!
# The radical of the PSU₃(5) centralizer supplement

The ambient two-quotient is cyclic: its faithful outer action intersects the
diagonal group of exponent three trivially. Component calculus makes the
local radical centralize the SL₂(5) residual. Consequently an intrinsic
double-centralizer bound in the simple socle puts the kernel of the radical's
map to the ambient quotient in the central involution. A central kernel and
cyclic image imply that the radical is abelian.

The intrinsic bound is supplied by the actual projective matrix calculation
in `Radical.InnerModel`, for arbitrary Hermitian forms over fields of order 25.
The final theorem discharges the abelian-radical premise of the marked S₅
quotient construction. The actor cardinalities and the SQTK hypothesis are
unnecessary for this structural step. Source: Aschbacher--Smith A.3.21(a), p.55,
and E.1.14(7), p.214, citing Aschbacher (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
variable {G : Type*} [Group G] [Finite G]

/-- The literal ambient two-quotient is cyclic, retaining every allowed
two-extension of the simple PSU₃ socle. -/
theorem socle_quotient_isCyclic [IsSimpleGroup (generalizedFitting G)]
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p) :
    IsCyclic (G ⧸ generalizedFitting G) := by
  let L := generalizedFitting G
  have hC : centralizer (L : Set G) = ⊥ :=
    SimpleSocle.centralizer_eq_bot (G := G) (nonabelian_of_model hp ho hmodel)
  have hP : IsPGroup 2 (G ⧸ L) :=
    isPGroup_quotient_of_sup_eq_top L T T.isPGroup' hLT
  obtain ⟨F, _, _, J, hcard, hc, ⟨e⟩⟩ := hmodel
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  let f : G ⧸ L →* MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (MulAut.outerCongr e).toMonoidHom.comp (MulAut.outerAction L)
  have hf : Function.Injective f :=
    (MulAut.outerCongr e).injective.comp (MulAut.outerAction_injective L hC)
  exact HermitianForm.FiveCentralizerRadical.isCyclic_of_outer_injective
    (P := G ⧸ L) J hp ho hcard hc hP f hf

/-- Component calculus places the actual local radical in the centralizer
of the actual embedded residual, with no commutativity assumption. -/
theorem centralizer_radical_le_residual_centralizer (L : Subgroup G) [L.Normal]
    {T : Sylow 2 G} (hLT : L ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p)
    (hmodel : ClassicalGroup.IsPSU L 3 p) {z : G} (hzL : z ∈ L)
    (hz : orderOf z = 2) (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let K := centralizerResidualOvergroup T z
    solvableRadical K ≤ centralizer (solvableResidual K : Set K) := by
  let K := centralizerResidualOvergroup T z
  let D := solvableResidual K
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨ec⟩ := inner_centralizer_residual_equiv L T hLT hp ho hlarge hmodel z hzL hz
  let e : D ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
    (centralizerResidualOvergroup_residualEquiv hTz).trans ec
  have hF : Nat.card (ZMod p) = p := Nat.card_zmod p
  let : IsQuasisimple D := Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
    (G := D) (F := ZMod p) (hF.symm ▸ hlarge) e
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  have hcomp : IsComponent K D := ⟨(inferInstance : D.Normal).isSubnormal, inferInstance⟩
  apply le_centralizer_iff.mp
  rcases hcomp.normal_dichotomy (solvableRadical K) with hle | hc
  · exact (Group.IsPerfect.not_isSolvable D
      (Group.isSolvable_of_isSolvable_injective (inclusion_injective hle))).elim
  · exact commutator_eq_bot_iff_le_centralizer.mp hc

/-- Abelianness reduces to the intrinsic centralizer of the embedded residual
in PSU₃(5). This is the only model premise left explicit. The actor hypotheses
are unnecessary for this structural implication. -/
theorem centralizer_radical_isMulCommutative_of_inner_bound
    [IsSimpleGroup (generalizedFitting G)]
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 5)
    {z : G} (hzL : z ∈ generalizedFitting G) (hzT : z ∈ (T : Subgroup G))
    (hz : orderOf z = 2) (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hinner : let w : generalizedFitting G := ⟨z, hzL⟩
      let C := centralizer ({w} : Set (generalizedFitting G))
      centralizer ((solvableResidual C).map C.subtype : Set (generalizedFitting G)) ≤
        zpowers w) :
    IsMulCommutative (solvableRadical (centralizerResidualOvergroup T z)) := by
  let L := generalizedFitting G
  let K := centralizerResidualOvergroup T z
  let R := solvableRadical K
  let w : L := ⟨z, hzL⟩
  let C := centralizer ({z} : Set G)
  let C₀ := centralizer ({w} : Set L)
  let f : C₀ →* C :=
    { toFun := fun x => ⟨x.val.val, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hD (d : solvableResidual C₀) : (d.val.val : G) ∈ (solvableResidual K).map K.subtype := by
    rw [centralizerResidualOvergroup_residual_map hTz]
    exact mem_map_of_mem C.subtype
      (map_solvableResidual_le f (mem_map_of_mem f d.property))
  have hRC := centralizer_radical_le_residual_centralizer L hLT (by decide) (by decide)
    (by decide : 3 < 5) hmodel hzL hz hTz
  let v : K := ⟨z, (show (T : Subgroup G) ≤ K from le_sup_right) hzT⟩
  have hv : v ∈ center K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (mem_centralizer_singleton_iff.mp
      (centralizerResidualOvergroup_le hTz k.property))
  let : IsCyclic (G ⧸ L) := socle_quotient_isCyclic hLT (by decide) (by decide) hmodel
  let q : R →* G ⧸ L := (QuotientGroup.mk' L).comp (K.subtype.comp R.subtype)
  apply q.isMulCommutative_of_isCyclic_of_ker_le_center
  intro r hr
  have hrL : (r.val : G) ∈ L := (QuotientGroup.eq_one_iff (N := L) r.val.val).mp hr
  have hrC : (⟨r.val.val, hrL⟩ : L) ∈
      centralizer ((solvableResidual C₀).map C₀.subtype : Set L) := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨a, ha, he⟩ := hD ⟨d, hd⟩
    apply Subtype.ext
    change (d.val : G) * r.val.val = r.val.val * d.val
    have he' : (a : G) = (d.val : G) := he
    rw [← he']
    exact congrArg (fun x : K => (x : G)) (hRC r.property a ha)
  have hrZ : r.val ∈ center K := by
    obtain ⟨n, hn⟩ := hinner hrC
    have hn' : z ^ n = r.val.val := congrArg (fun x : L => (x : G)) hn
    have he : v ^ n = r.val := Subtype.ext hn'
    exact he ▸ (center K).zpow_mem hv n
  rw [mem_center_iff]
  intro s
  exact Subtype.ext (mem_center_iff.mp hrZ s.val)

/-- The radical of the actual involution-centralizer supplement is abelian
for every permitted ambient two-extension of the simple PSU₃(5) socle.
This supplies the radical premise of the marked-quotient construction. -/
theorem centralizer_radical_isMulCommutative
    [IsSimpleGroup (generalizedFitting G)]
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 5)
    {z : G} (hzL : z ∈ generalizedFitting G) (hzT : z ∈ (T : Subgroup G))
    (hz : orderOf z = 2) (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    IsMulCommutative (solvableRadical (centralizerResidualOvergroup T z)) := by
  apply centralizer_radical_isMulCommutative_of_inner_bound hLT hmodel hzL hzT hz hTz
  exact inner_residual_centralizer_le_zpowers hmodel ⟨z, hzL⟩
    ((Subgroup.orderOf_coe (⟨z, hzL⟩ : generalizedFitting G)).symm.trans hz)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
