module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductExchange
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.SL2.BinarySmallModels
/-!
# The original natural coordinates under the whole component orbit

The original component marking extends to its actual two-factor orbit, with
actor map the first projection of the original marked A₅ product quotient.
The opposite component centralizes the moved numerator. Equality of the two
actions is checked on these generators, preserving the given coordinate map
and its actual central kernel. No selected E.2.3 source is used.

Source: Aschbacher–Smith10.1.1 and10.1.2(5), printed pp.741–742.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
  (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
  {K : Type*} [Field K] [CharP K 2]
local instance omegaEntranceAlgebra : Algebra (ZMod 2) K := ZMod.algebra K 2
local instance omegaEntranceMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
variable (f : alternatingGroup (Fin 5) ≃* SL(2,K))
  (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
    (SL2.BinarySmall.natural.comp
      (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))

set_option backward.isDefEq.respectTransparency false in
def source_original_natural_first_orbit_section : BinaryConjugationSection (localOrbit T L) ⁅D.fullModule,L⁆ (sourceMovedFixed D)
    (SL2.BinarySmall.natural.comp
      (f.toMonoidHom.comp ((MonoidHom.fst _ _).comp
        (originalA5ProductProjection D e hn ht htn)))) := by
  let R := localOrbit T L
  let W := ⁅D.fullModule,L⁆
  let B := L.map (MulAut.conj t).toMonoidHom
  let q := originalA5ProductProjection D e hn ht htn
  let φ := SL2.BinarySmall.natural.comp
    (f.toMonoidHom.comp ((MonoidHom.fst _ _).comp q))
  have hpair : L ⊔ B = R :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht htn).symm
  have hgen : L.subgroupOf R ⊔ B.subgroupOf R = ⊤ := by
    rw [←subgroupOf_sup (le_componentOrbit L T) (le_sup_right.trans hpair.le),hpair,subgroupOf_self]
  have hSW : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (W : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = _
    have hV : D.fullModule.map (MulAut.conj g).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp
        (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T hg.1))
    have hL : L.map (MulAut.conj g).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp hg.2
    rw [map_commutator,hV,hL]
  have htwice := conjugate_twice_eq_of_index_two W (T : Subgroup G)
    (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn) hSW ht
  have hBC : B ≤ centralizer (W : Set G) := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hcross
    rw [htwice,Theory.GroupTheory.map_centralizer_equiv] at hh
    exact le_centralizer_iff.mp hh
  have hRW : R ≤ normalizer (W : Set G) := by
    rw [←hpair]
    exact sup_le n.normalized (hBC.trans (Subgroup.centralizer_le_normalizer _))
  have hRZ : R ≤ normalizer (sourceMovedFixed D : Set G) := by
    rw [←hpair]
    apply sup_le
    · exact (le_inf L.le_normalizer n.normalized).trans (source_original_moved_fixed_normalizer D)
    · exact (hBC.trans (centralizer_le n.kernel_le)).trans (Subgroup.centralizer_le_normalizer _)
  let η := (n.exists_original_quotient_action hRW hRZ).choose
  have hη := (n.exists_original_quotient_action hRW hRZ).choose_spec
  have hA : L.subgroupOf R ≤ η.eqLocus φ := by
    intro a ha
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw⟩ := n.onto (Multiplicative.ofAdd v)
    have hw' : (n.coordinates w).toAdd = v := congrArg Multiplicative.toAdd hw
    rw [←hw',hη]
    have he := n.equivariant (⟨a,ha⟩ : L) w
    change (n.coordinates _).toAdd = SL2.BinarySmall.natural (f (q a).1) _
    rw [show q a = (e (QuotientGroup.mk' _ (⟨a,ha⟩ : L)),1) from
      originalA5ProductProjection_first D e hn ht htn (⟨a,ha⟩ : L)]
    exact he
  have hB : B.subgroupOf R ≤ η.eqLocus φ := by
    intro b hb
    obtain ⟨l,hl,hlb⟩ := mem_map.mp hb
    have hb' : b = originalConjugateOrbitInclusion ht (⟨l,hl⟩ : L) := Subtype.ext hlb.symm
    have hqb : (q b).1 = 1 := by
      rw [hb',show q (originalConjugateOrbitInclusion ht (⟨l,hl⟩ : L)) =
        (1,e (QuotientGroup.mk' _ (⟨l,hl⟩ : L))) from
          originalA5ProductProjection_second D e hn ht htn (⟨l,hl⟩ : L)]
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw⟩ := n.onto (Multiplicative.ofAdd v)
    have hw' : (n.coordinates w).toAdd = v := congrArg Multiplicative.toAdd hw
    rw [←hw',hη]
    change (n.coordinates _).toAdd = SL2.BinarySmall.natural (f (q b).1) _
    rw [hqb,map_one,map_one]
    change (n.coordinates _).toAdd = (n.coordinates w).toAdd
    congr 2
    apply Subtype.ext
    change (b:G)*w*(b:G)⁻¹ = w
    have hbcomm : (b:G)*(w:G) = (w:G)*(b:G) := (hBC hb w w.property).symm
    rw [hbcomm,mul_inv_cancel_right]
  have heq : η = φ := by
    apply MonoidHom.ext
    intro x
    exact (sup_le hA hB) (hgen.symm ▸ mem_top x)
  exact { n with
    section_le := n.section_le.trans (le_componentOrbit L T)
    normalized := hRW
    equivariant := by
      intro r w
      change (n.coordinates _).toAdd = φ r (n.coordinates w).toAdd
      rw [←heq]
      exact (hη r w).symm }
end CFSG.Quasithin.Chapter10
