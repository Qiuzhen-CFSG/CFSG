module
public import CFSG.Quasithin.Chapter10.SourceA5PointLinear
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion

/-!
# The linear row feeds the original point-centralizer alternative

The conjugate moved elementary module centralizes each of its elements, so
normalization of the containing component follows from the original
point-centralizer hypothesis. Linear perfect-cover rigidity then supplies
the common centralizer alternative in Aschbacher–Smith, proof of 10.2.9,
pp.750–751 (1 March 2004 manuscript). No separate embedding marking is needed.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual conjugate moved module supplies the common alternative for
any perfect containing component with central quotient PSL3(4). -/
theorem source_a5_point_linear_alternative
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (t : G)
    (I : Subgroup G) [Group.IsPerfect I] (hLI : L ≤ I)
    (eI : I ⧸ center I ≃* Matrix.PSL3Four.PSL)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G)) :
    SourceA5PointComponentAlternative D e t I := by
  let := source_original_full_moved_elementary D
  let U := (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  have hUC : U ≤ centralizer ({v} : Set G) := by
    intro u hu y hy
    have he : y = v := Set.mem_singleton_iff.mp hy
    rw [he]
    exact U.le_centralizer hu v hv
  exact .common (source_a5_psl3Four_containing_centralizer D e hLI eI U
    (hUC.trans hNI) hcross)

end CFSG.Quasithin.Chapter10
