module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.FourNormalClosure
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.Generation
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.CoreContainment
public import CFSG.Quasithin.Chapter5.Section03LinearSource.MarkedNormalClosure
public import CFSG.Quasithin.Chapter5.Section03LinearSource.QuaternionCentralizer
public import CFSG.Quasithin.Chapter5.Section03LinearSource.NormalClosureIndex
public import CFSG.Quasithin.Chapter5.Section03LinearSource.FlagControl
public import CFSG.Quasithin.Chapter5.Section03LinearSource.QuaternionContradiction

/-!
# Closing the exceptional linear centralizer branch

In degree two, the actual central-line normal closure either gives the
required centralizer bound or equals the same marked quaternion subgroup.
The abelian case uses central-line fusion; the nonabelian alternatives
come from the native Sylow geometry. In the quaternion case the original
normal closure gives [C_G(z):T] ≥ 4, while the same marked root plane and
its quaternion intersection give a full binary flag. Its stabilizer is
a two-group. Transporting the native quaternion factors into C_G(z) and
using the original plane's weak closure yields the order-nine contradiction.

Together with the proved larger-field branch and local central-line
transitivity this proves the full involution-centralizer intersection
bound at every original degree, with both comparison orientations.
Full-normalizer realization, ambient generation and linear recognition
are separate subsequent steps. Source: Aschbacher--Smith §5.3.7, printed
pp.660--661 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
open Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3.LinearAmbientGeometry
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax

/-- Once the normal closure stays in S, its abelian and nonabelian cases
both give the original full-normalizer centralizer bound. -/
theorem Preparation.linear_four_centralizer_le_inter_of_normalClosure_le
    (hn : n=2) (c : Chapter5.Section03ExceptionalSylowModel.MarkedCopy G)
    (hT : c.carrier=(T : Subgroup G)) (hS : c.S=sourceS L H)
    (hZ : c.Z=centerIn (sourceS L H))
    (hzT : (T : Subgroup G) ≤ centralizer ({c.z} : Set G))
    (hle : linearCentralLineClosure L H c.z ≤ sourceS L H) :
    centralizer ({c.z} : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  have hz2 : orderOf c.z=2 := orderOf_eq_prime c.z_sq c.z_ne_one
  have hz : c.z ∈ centerIn (sourceS L H) := hZ ▸ c.z_mem_Z
  by_cases hab : IsMulCommutative (linearCentralLineClosure L H c.z)
  · exact d.linear_four_centralizer_le_inter_of_abelian_normalClosure h hH hp F hm hF he hmax
      hn c.z hz2 hz hzT hab
  have hcore := d.linear_four_normalClosure h hH hp F hm hF he hmax hn c.z hz2 hz hzT
  have hUT : linearCentralLineClosure L H c.z ≤ c.carrier := by
    rw [hT]
    exact hcore.1.trans
      (d.linear_centralizer_core_displacement h hH hp F hm hF he hmax c.z hz hzT).1
  have hnorm := le_normalizer_conjugateSpanBy (centerIn (sourceS L H))
    (centralizer ({c.z} : Set G))
  have hnT : c.carrier ≤ normalizer (linearCentralLineClosure L H c.z : Set G) := by
    rw [hT]
    exact hzT.trans hnorm
  have hZU : c.Z ≤ linearCentralLineClosure L H c.z := hZ ▸ le_conjugateSpanBy _ _
  have hcenter : centerIn (linearCentralLineClosure L H c.z) = centerIn (sourceS L H) := by
    rcases Chapter5.Section03LinearSource.marked_normalClosure_alternatives c _
      hUT hnT hZU hcore.2 hab with ⟨_,hzU⟩ | hQ
    · exact hzU.trans hZ
    · have hQS : c.Q ≤ c.S := by rwa [hQ,←hS] at hle
      have hh := (map_le_map_iff_of_injective c.embedding_injective).mp hQS
      have hnaQ : ¬ Matrix.PSL3Four.SylowModel.Q ≤ Matrix.PSL3Four.SylowModel.S := by
        intro hq
        have ha := hq Matrix.PSL3Four.SylowModel.fieldD.property
        have heq := (Matrix.PSL3Four.SylowModel.mem_S _).mp ha
        change Matrix.PSL3Four.SylowModel.τ=1 at heq
        have hne : Matrix.PSL3Four.SylowModel.τ ≠ 1 := by decide
        exact hne heq
      exact (hnaQ hh).elim
  apply Chapter5.Section03CentralizerExceptional.centralizer_le_of_normal_closure_center
    c.z (centerIn (sourceS L H)) (linearCentralLineClosure L H c.z)
    (normalizer (L : Set G)) (normalizer (residual H : Set G)) hnorm
  · rwa [←centerIn_eq_map_center]
  · exact (d.linear_center_normalizer h hH hp F hm hF he hmax).le

/-- The orbit lower bound uses the index of the original Sylow subgroup
inside the actual involution centralizer. -/
theorem Preparation.linear_four_quaternion_index_lower
    (c : Chapter5.Section03ExceptionalSylowModel.MarkedCopy G)
    (hZ : c.Z=centerIn (sourceS L H))
    (hzT : (T : Subgroup G) ≤ centralizer ({c.z} : Set G))
    (hQ : linearCentralLineClosure L H c.z=c.Q) :
    4 ≤ (T : Subgroup G).relIndex (centralizer ({c.z} : Set G)) := by
  let D := centralizer ({c.z} : Set G)
  have hz2 : orderOf c.z=2 := orderOf_eq_prime c.z_sq c.z_ne_one
  have hz : c.z ∈ centerIn (sourceS L H) := hZ ▸ c.z_mem_Z
  have hZD : c.Z ≤ D := by
    rw [hZ]
    exact fun x hx => mem_centralizer_singleton_iff.mpr (hx.2 c.z hz.1).symm
  let Z := c.Z.subgroupOf D
  let zD : D := ⟨c.z,mem_centralizer_singleton_iff.mpr rfl⟩
  let C := zpowers zD
  have hc : C ≤ center D := zpowers_le_of_mem (mem_center_iff.mpr (fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.mp x.property)))
  let : C.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hc hx) g,mul_assoc,mul_inv_cancel,mul_one]
    exact hx⟩
  have hZV : c.Z ≤ c.V₁ := by rw [←c.V₁_inf_V₂];exact inf_le_left
  let : IsElementaryAbelian 2 c.Z := IsElementaryAbelian.of_injective
    (inclusion hZV) (inclusion_injective hZV)
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf hZD
  have hTZ : (T : Subgroup G) ≤ normalizer (c.Z : Set G) := by
    rw [hZ,d.linear_center_normalizer h hH hp F hm hF he hmax]
    exact le_inf h.sylow_normalizes (hH.1.1.2.trans (le_normalizer_residual H))
  have hnZ : (T.subtype hzT : Subgroup D) ≤ normalizer (Z : Set D) := by
    intro x hx
    exact (subgroupOf_normalizer_eq hZD).le (hTZ hx)
  have hcl : normalClosure (Z : Set D)=c.Q.subgroupOf D := by
    rw [normalClosure_subgroupOf_eq_conjugateSpanBy c.Z D hZD]
    rw [hZ]
    exact congrArg (fun U : Subgroup G => U.subgroupOf D) hQ
  have hQD : c.Q ≤ D := hQ ▸ conjugateSpanBy_le_self (hZ ▸ hZD)
  have hcard : Nat.card (normalClosure (Z : Set D))=32 := by
    rw [hcl,Nat.card_congr (subgroupOfEquivOfLe hQD).toEquiv]
    change Nat.card (Matrix.PSL3Four.SylowModel.Q.map c.embedding)=32
    rw [card_map_of_injective c.embedding_injective,Matrix.PSL3Four.SylowModel.card_Q]
  apply Chapter5.Section03LinearSource.four_normalClosure_index_lower (T.subtype hzT) Z C
  · exact Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.qtke.evenCharacteristic T) (isTwoLocal_involution_centralizer hz2) hzT)
  · exact hnZ
  · exact (Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv).trans c.card_Z
  · rw [Nat.card_zpowers,Subgroup.orderOf_mk,hz2]
  · exact zpowers_le_of_mem c.z_mem_Z
  · exact hc
  · exact hcard

/-- The degree-two failure alternative is now the actual marked quaternion
normal closure in the original involution centralizer, with no geometric
premise. The same mark retains both original root planes. -/
theorem Preparation.linear_four_centralizer_or_quaternion_closure (hn : n=2) :
    (∃ z : G, orderOf z=2 ∧ z ∈ centerIn (sourceS L H) ∧
      centralizer ({z} : Set G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G)) ∨
    ∃ c : Chapter5.Section03ExceptionalSylowModel.MarkedCopy G,
      c.carrier=(T : Subgroup G) ∧ c.S=sourceS L H ∧
      ((c.V₁=L.pCoreIn 2 ∧ c.V₂=(residual H).pCoreIn 2) ∨
       (c.V₁=(residual H).pCoreIn 2 ∧ c.V₂=L.pCoreIn 2)) ∧
      c.Z=centerIn (sourceS L H) ∧ orderOf c.z=2 ∧
      (T : Subgroup G) ≤ centralizer ({c.z} : Set G) ∧
      linearCentralLineClosure L H c.z=c.Q ∧
      c.Q ≤ (centralizer ({c.z} : Set G)).pCoreIn 2 ∧
      centralizer ({c.z} : Set G) ≤ normalizer (c.Q : Set G) ∧
      centralizer ({c.z} : Set G) ⊓ centralizer (c.Q : Set G) ≤ c.Q ∧
      4 ≤ (T : Subgroup G).relIndex (centralizer ({c.z} : Set G)) := by
  rcases d.linear_four_sylow_alternative h hH hp F hm hF he hmax hn with hST | hc
  · obtain ⟨z,hz,hz2,_⟩ := d.linear_exists_sylow_central_involution h hH hp F hm hF he hmax
    exact Or.inl ⟨z,hz2,hz,d.linear_centralizer_le_inter_of_sourceS_eq_sylow
      h hH hp F hm hF he hmax hST z hz2 hz⟩
  obtain ⟨c,hT,hS,hplanes,hZ,hz2,hzT⟩ := hc
  have hz : c.z ∈ centerIn (sourceS L H) := hZ ▸ c.z_mem_Z
  by_cases hle : linearCentralLineClosure L H c.z ≤ sourceS L H
  · exact Or.inl ⟨c.z,hz2,hz,
      d.linear_four_centralizer_le_inter_of_normalClosure_le h hH hp F hm hF he hmax
        hn c hT hS hZ hzT hle⟩
  by_cases hab : IsMulCommutative (linearCentralLineClosure L H c.z)
  · exact Or.inl ⟨c.z,hz2,hz,
      d.linear_four_centralizer_le_inter_of_abelian_normalClosure h hH hp F hm hF he hmax
        hn c.z hz2 hz hzT hab⟩
  have hcore := d.linear_four_normalClosure h hH hp F hm hF he hmax hn c.z hz2 hz hzT
  have hUT : linearCentralLineClosure L H c.z ≤ c.carrier := by
    rw [hT]
    exact hcore.1.trans
      (d.linear_centralizer_core_displacement h hH hp F hm hF he hmax c.z hz hzT).1
  have hnorm := le_normalizer_conjugateSpanBy (centerIn (sourceS L H))
    (centralizer ({c.z} : Set G))
  have hnT : c.carrier ≤ normalizer (linearCentralLineClosure L H c.z : Set G) := by
    rw [hT]
    exact hzT.trans hnorm
  have hZU : c.Z ≤ linearCentralLineClosure L H c.z := hZ ▸ le_conjugateSpanBy _ _
  have hQ : linearCentralLineClosure L H c.z=c.Q := by
    rcases Chapter5.Section03LinearSource.marked_normalClosure_alternatives c _
      hUT hnT hZU hcore.2 hab with ⟨hh,_⟩ | hh
    · exact (hle (hS ▸ hh)).elim
    · exact hh
  refine Or.inr ⟨c,hT,hS,hplanes,hZ,hz2,hzT,hQ,hQ ▸ hcore.1,hQ ▸ hnorm,?_,
    d.linear_four_quaternion_index_lower h hH hp F hm hF he hmax c hZ hzT hQ⟩
  apply Chapter5.Section03LinearSource.marked_quaternion_centralizer_le c T hT
    (centralizer ({c.z} : Set G)) hzT
    ((hQ ▸ hcore.1).trans (pCoreIn_le 2 _)) (hQ ▸ hnorm)
  exact Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
    (h.qtke.evenCharacteristic T) (isTwoLocal_involution_centralizer hz2) hzT)

/-- Normality of the same quaternion closure supplies a binary flag
preserved by the local involution centralizer, forcing that local group
to be a two-group. -/
theorem Preparation.linear_four_local_normalizer_isPGroup
    (c : Chapter5.Section03ExceptionalSylowModel.MarkedCopy G)
    (hplanes : (c.V₁=L.pCoreIn 2 ∧ c.V₂=(residual H).pCoreIn 2) ∨
       (c.V₁=(residual H).pCoreIn 2 ∧ c.V₂=L.pCoreIn 2))
    (hZ : c.Z=centerIn (sourceS L H))
    (hnQ : centralizer ({c.z} : Set G) ≤ normalizer (c.Q : Set G)) :
    IsPGroup 2 (centralizer ({c.z} : Set G) ⊓ normalizer (c.V₁ : Set G) : Subgroup G) := by
  obtain ⟨i,hi⟩ : ∃ i : Fin 2, c.V₁=(![L,residual H] i).pCoreIn 2 := by
    rcases hplanes with ⟨h1,_⟩ | ⟨h1,_⟩
    · exact ⟨0,h1⟩
    · exact ⟨1,h1⟩
  have hnV : normalizer (c.V₁ : Set G)=normalizer (![L,residual H] i : Set G) := by
    rw [hi]
    fin_cases i
    · exact (d.linear_root_normalizers h hH hp F hm hF he hmax).1
    · exact (d.linear_root_normalizers h hH hp F hm hF he hmax).2.1
  have hself : centralizer (c.V₁ : Set G) ≤ c.V₁ := by
    rw [hi]
    fin_cases i
    · exact (d.linear_root_centralizers h hH hp F hm hF he hmax).1.le
    · exact (d.linear_root_centralizers h hH hp F hm hF he hmax).2.le
  apply Chapter5.Section03LinearSource.marked_flag_normalizer_isPGroup c
    (centralizer ({c.z} : Set G) ⊓ normalizer (c.V₁ : Set G))
    inf_le_left _ (inf_le_left.trans hnQ) inf_le_right hself
  rw [hZ,d.linear_center_normalizer h hH hp F hm hF he hmax,hnV]
  exact d.linear_normalizer_centralizer_le_inter h hH hp F hm hF he hmax i c.z
    (hZ ▸ c.z_mem_Z) c.z_ne_one

/-- Source §5.3.7 in the exceptional degree-two row. The same marked Sylow
supplies the quaternion factors and binary flag, the genuine normal closure
gives the source index bound, and weak closure closes the order-nine
contradiction inside the literal involution centralizer. -/
theorem Preparation.linear_four_exists_centralizer_le_inter (hn : n=2) :
    ∃ z : G, orderOf z=2 ∧ z ∈ centerIn (sourceS L H) ∧
      centralizer ({z} : Set G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  rcases d.linear_four_centralizer_or_quaternion_closure h hH hp F hm hF he hmax hn with hg | hc
  · exact hg
  obtain ⟨c,hT,_,hplanes,hZ,_,hzT,_,hQcore,hnQ,hself,hlower⟩ := hc
  have hmem : c.V₁ ∈ ({L.pCoreIn 2,(residual H).pCoreIn 2} : Set (Subgroup G)) := by
    rcases hplanes with ⟨h1,_⟩ | ⟨h1,_⟩ <;> simp [h1]
  exact (Chapter5.Section03LinearSource.marked_quaternion_contradiction c T hT
    (centralizer ({c.z} : Set G)) hzT (hQcore.trans (pCoreIn_le 2 _)) hnQ hself hlower
    (d.linear_root_planes_weakly_closed h hH hp F hm hF he hmax c.V₁ hmem)
    (d.linear_four_local_normalizer_isPGroup h hH hp F hm hF he hmax c hplanes hZ hnQ)).elim

/-- Every original degree, including two, supplies the source involution
centralizer bound without any additional core or index premise. -/
theorem Preparation.linear_exists_centralizer_le_inter :
    ∃ z : G, orderOf z=2 ∧ z ∈ centerIn (sourceS L H) ∧
      centralizer ({z} : Set G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  by_cases hn : n=2
  · exact d.linear_four_exists_centralizer_le_inter h hH hp F hm hF he hmax hn
  have hnlarge : 2<n := by have hh := h.exponent;omega
  obtain ⟨z,hz,hz2,hzT⟩ := d.linear_exists_sylow_central_involution h hH hp F hm hF he hmax
  exact ⟨z,hz2,hz,d.linear_centralizer_le_inter_of_large_central h hH hp F hm hF he hmax
    hnlarge z hz2 hz hzT⟩

/-- Source §5.3.7 at every original degree and in either marked orientation.
All nonidentity central-line involutions have their full ambient centralizer
in the original full-normalizer intersection. -/
theorem Preparation.linear_centralizer_le_inter
    (z : G) (hz2 : orderOf z=2) (hz : z ∈ centerIn (sourceS L H)) :
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  obtain ⟨w,hw2,hw,hcw⟩ := d.linear_exists_centralizer_le_inter h hH hp F hm hF he hmax
  have hw1 : w≠1 := by intro hh;simp [hh] at hw2
  have hz1 : z≠1 := by intro hh;simp [hh] at hz2
  obtain ⟨g,hg,hgw⟩ := d.linear_center_transitive h hH hp F hm hF he hmax w z hw hz hw1 hz1
  let M := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  intro x hx
  have hc : g⁻¹*x*g ∈ centralizer ({w} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hh := mem_centralizer_singleton_iff.mp hx
    rw [←hgw] at hh
    calc
      (g⁻¹*x*g)*w = g⁻¹*(x*(g*w*g⁻¹))*g := by group
      _ = g⁻¹*((g*w*g⁻¹)*x)*g := by rw [hh]
      _ = w*(g⁻¹*x*g) := by group
  have hm : g*(g⁻¹*x*g)*g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg (hcw hc)) (M.inv_mem hg)
  rwa [show g*(g⁻¹*x*g)*g⁻¹=x from by group] at hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
