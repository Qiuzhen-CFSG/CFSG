module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalRow.Quotient
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductExchange
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.SL2.BinarySmallModels
/-!
# The original natural component action on its two-component orbit

The crossed-factor hypothesis extends the given section to the actual
orbit L₀, using the first projection of its marked quotient. The Sylow
exchanger swaps the two quotient factors, with the automorphism induced by
t² retained. The map identities are proved on the original component and
its prescribed conjugate, then extended through their literal join.

This generalizes `OmegaEntrance.FirstSection` and
`SourceA5OriginalProductExchange`. The quotient markings are discharged by
`source_original_natural_pair_quotient` in the seed-centralizer application.
Source: Aschbacher–Smith D.3.6–7 and 10.1.1–2, pp.196–199,741–742.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
  (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
  {K : Type*} [Field K] [CharP K 2]
local instance omegaEntranceAlgebra : Algebra (ZMod 2) K := ZMod.algebra K 2
local instance omegaEntranceMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
variable (e : (L ⧸ pCore 2 L) ≃* SL(2,K))
  (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
    (SL2.BinarySmall.natural.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

set_option backward.isDefEq.respectTransparency false in
@[expose] def source_original_natural_first_orbit_section
    (q : localOrbit T L →* (SL(2,K) × SL(2,K)))
    (hfirst : ∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1))
    (hsecond : ∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l))) : BinaryConjugationSection (localOrbit T L) ⁅D.fullModule,L⁆ (sourceMovedFixed D)
    (SL2.BinarySmall.natural.comp
      ((MonoidHom.fst _ _).comp q)) := by
  let R := localOrbit T L
  let W := ⁅D.fullModule,L⁆
  let B := L.map (MulAut.conj t).toMonoidHom
  let φ := SL2.BinarySmall.natural.comp
    ((MonoidHom.fst _ _).comp q)
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
    change (n.coordinates _).toAdd = SL2.BinarySmall.natural ((q a).1) _
    rw [show q a = (e (QuotientGroup.mk' _ (⟨a,ha⟩ : L)),1) from
      hfirst (⟨a,ha⟩ : L)]
    exact he
  have hB : B.subgroupOf R ≤ η.eqLocus φ := by
    intro b hb
    obtain ⟨l,hl,hlb⟩ := mem_map.mp hb
    have hb' : b = originalConjugateOrbitInclusion ht (⟨l,hl⟩ : L) := Subtype.ext hlb.symm
    have hqb : (q b).1 = 1 := by
      rw [hb',show q (originalConjugateOrbitInclusion ht (⟨l,hl⟩ : L)) =
        (1,e (QuotientGroup.mk' _ (⟨l,hl⟩ : L))) from
          hsecond (⟨l,hl⟩ : L)]
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw⟩ := n.onto (Multiplicative.ofAdd v)
    have hw' : (n.coordinates w).toAdd = v := congrArg Multiplicative.toAdd hw
    rw [←hw',hη]
    change (n.coordinates _).toAdd = SL2.BinarySmall.natural ((q b).1) _
    rw [hqb,map_one]
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

omit [CharP K 2] in
/-- Exact exchange of the marked product coordinates under the original t. -/
theorem source_natural_pair_conjugate (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,K))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (q : localOrbit T L →* (SL(2,K) × SL(2,K)))
    (hfirst : ∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1))
    (hsecond : ∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l)))
    (x : localOrbit T L) :
    q (originalOrbitConjugation ht x) =
      ((e.symm.trans ((QuotientGroup.congr _ _ (originalSquareConjugation D hn ht)
      (pCore_map_iso 2 (originalSquareConjugation D hn ht))).trans e)) (q x).2,
        (q x).1) := by
  let R := localOrbit T L
  let A := L.subgroupOf R
  let B := (L.map (MulAut.conj t).toMonoidHom).subgroupOf R
  let τ := originalOrbitConjugation (L := L) ht
  let β := (e.symm.trans ((QuotientGroup.congr _ _ (originalSquareConjugation D hn ht)
      (pCore_map_iso 2 (originalSquareConjugation D hn ht))).trans e))
  let f := q.comp τ.toMonoidHom
  let g := ((β.toMonoidHom.comp (MonoidHom.snd _ _)).prod (MonoidHom.fst _ _)).comp q
  have hp : L ⊔ L.map (MulAut.conj t).toMonoidHom = R :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht htn).symm
  have hgen : A ⊔ B = ⊤ := by
    rw [←subgroupOf_sup (le_componentOrbit L T) (le_sup_right.trans hp.le),hp,subgroupOf_self]
  have hA : A ≤ f.eqLocus g := by
    intro a ha
    let l : L := ⟨a,ha⟩
    change q (τ a) = (β (q a).2,(q a).1)
    have hfirst : q a = (e (QuotientGroup.mk' _ l),1) :=
      hfirst l
    have hsecond : q (τ a) = (1,e (QuotientGroup.mk' _ l)) :=
      hsecond l
    rw [hfirst,hsecond]
    exact Prod.ext β.map_one.symm rfl
  have hB : B ≤ f.eqLocus g := by
    intro b hb
    obtain ⟨l,hl,he⟩ := mem_map.mp hb
    let l' : L := ⟨l,hl⟩
    have hb' : b = originalConjugateOrbitInclusion ht l' := Subtype.ext he.symm
    subst b
    change q (τ (originalConjugateOrbitInclusion ht l')) =
      (β (q (originalConjugateOrbitInclusion ht l')).2,
        (q (originalConjugateOrbitInclusion ht l')).1)
    rw [show q (originalConjugateOrbitInclusion ht l') = (1,e (QuotientGroup.mk' _ l')) from
      hsecond l']
    let l₂ := originalSquareConjugation D hn ht l'
    have he₂ : τ (originalConjugateOrbitInclusion ht l') =
        (⟨l₂,le_componentOrbit L T l₂.property⟩ : R) := by
      apply Subtype.ext
      change t * (t * l * t⁻¹) * t⁻¹ = (t*t) * l * (t*t)⁻¹
      simp only [mul_inv_rev,mul_assoc]
    rw [he₂]
    change q ⟨l₂,le_componentOrbit L T l₂.property⟩ = (β (e (QuotientGroup.mk' _ l')),1)
    rw [show q ⟨l₂,le_componentOrbit L T l₂.property⟩ = (e (QuotientGroup.mk' _ l₂),1) from
      hfirst l₂]
    congr 1
    change e (QuotientGroup.mk' _ l₂) =
      e ((QuotientGroup.congr _ _ (originalSquareConjugation D hn ht)
        (pCore_map_iso 2 (originalSquareConjugation D hn ht))) (e.symm (e (QuotientGroup.mk' _ l'))))
    rw [e.symm_apply_apply]
    rfl
  exact (sup_le hA hB) (hgen.symm ▸ mem_top x)
end CFSG.Quasithin.Chapter10.MovingHall
