module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Complete
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.Complete
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Linear
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Symplectic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.RootClosure
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Witness.G2Source

/-!
# The two classical chosen-natural contradictions

The original marked flag and preceding source geometry give the independent
nonabelianness implication of 11.5.3(3). In the linear case, reselect H inside
N_G(V₁) with O²(H) centralizing V₁ and the required component-residual
alternative, then apply the complete SL₃ closure proof. In the symplectic
case the root and full-image branches give abelianness using the genuine
nonbinary C.1.32 MS-pair classification.

For both actions we construct the literal KT member of H(L₁T,M), prove
O²(KT)≤K using relative normality, and apply the earlier radical corank
bound. The proved amalgam argument gives K=L₁, contradicting 11.5.3(3).
Neither abelianness, nonabelianness nor K=L₁ is an input. The field-four
exceptional component rows and full SL₃ center are retained.

These are conditional source implications on the actual Chapter12 chosen
quotient. Earlier flag, Cartan and shadow conclusions remain explicit and
belong to qt-d-1222-natural-local-geometry, qt-d-1222-natural-shadow-reduction
and qt-d-1222-natural-closure. The Sp₄ recognition premise remains with
qt-c132-nonbinary-symplectic. Final discharge and the three-row source
application remain with qt-d-1222-nonbinary-natural and its Chapter12 owners;
this module does not assert 11.0.1 from NonbinaryNaturalInput alone.
Source: Aschbacher--Smith, 11.5.3--8 and 12.2.2,
refs/quasithin.pdf, printed pp.779--784,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

private theorem radicalCorank_of_preceding
    (s : E.CartanPrecedingGeometry) (hlt : E.L₁ < E.K) :
    Amalgam.OddGeometry.RadicalCorank E := by
  let J : Subgroup G := E.K ⊔ (T : Subgroup G)
  have hJG : J ≤ E.G₁ := sup_le E.K_le_G₁ s.flag.sylow_normalizes_point
  have hJK : J ≤ normalizer (E.K : Set G) := hJG.trans E.G₁_normalizes_K
  let : (E.K.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJK
  have hsup : E.K.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show E.K ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hp := isPGroup_quotient_of_sup_eq_top (E.K.subgroupOf J)
    ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype hsup
  have hr : (pResidual 2 J).map J.subtype ≤ E.K := by
    have hle : pResidual 2 J ≤ E.K.subgroupOf J := sInf_le ⟨inferInstance, hp⟩
    simpa only [map_subgroupOf_eq_of_le (show E.K ≤ J from le_sup_left)] using
      (show (pResidual 2 J).map J.subtype ≤ (E.K.subgroupOf J).map J.subtype from
        map_mono hle)
  have hpointJ : E.V₁ ≤ J := E.V₁_le.trans (D.le_sylow.trans le_sup_right)
  have hpCore : E.V₁ ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      (@IsElementaryAbelian.isPGroup 2 _ _ (D.centralQuotientPreimage_elementary E.point))
      hpointJ hJG
  have hJH : J ∈ Chapter1.H G := by
    intro hz
    exact D.centralQuotientPreimage_ne_bot E.point s.flag.point_nonzero
      (bot_unique (hz ▸ hpCore))
  have hout : ¬ J ≤ E.M := fun h => s.strict_escape hlt (le_sup_left.trans h)
  have hH : J ∈ Chapter1.HOutside G
      ((E.L₁ ⊔ (T : Subgroup G) : Subgroup G) : Set G) (E.M : Set G) :=
    ⟨⟨hJH, sup_le_sup_right (le_conjugateSpanBy E.L₁ E.G₁) _⟩, hout⟩
  intro A hA hAR
  let : IsElementaryAbelian 2 A := hA
  exact E.elementary_corank_le_one_of_source_geometry J hH hJG hr
    s.local_model s.refinement (fun _ => s.no_triangle) s.strict_radical A hAR

/-- Conditional SL₃ exclusion from the preceding source geometry. -/
theorem nonbinary_sl3_impossible_of_preceding_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : E.CartanPrecedingGeometry)
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (f : InvariantFlag (.sl3 m)) (hm : Amalgam.Even.FlagMatch E f)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hNV : normalizer (V : Set G) ≤ E.M)
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1)
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v)
    (hcomp : E.Kz = E.K)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hobstruction : Chapter11.Source.WeakClosureObstruction (T : Subgroup G) V E.V₁ E.H)
    (hlocalM : @ChapterE.localM _ _ V D.elementary = E.input.field.degree)
    (hn : ChapterE.generationParameter E.H = 1)
    (hsplit : L ⊓ E.G₁ = (E.L₁ ⊔ L.pCoreIn 2) ⊔ E.X)
    (hLi : Chapter11.Source.ComponentIn E.M₁ E.L₁)
    (hres : pointResidual L E.z = E.L₁)
    (horbit : ∀ u ∈ E.V₁, u ≠ 1 → ∃ x ∈ L ⊓ E.G₁, (MulAut.conj x) E.z = u)
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞)) :
    False := by
  let F₀ : Nonabelian.MarkedFlag E :=
    ⟨.sl3 m, f, hm.point.symm, hm.plane.symm, hm.threeSpace.symm⟩
  have hnonabelian : E.K = E.L₁ → ¬ IsMulCommutative E.W :=
    Nonabelian.not_isMulCommutative_of_K_eq F₀ hfixed hNV hz hz1 htrans hcomp
      (Preliminary.seed_ti D { E.input with many := hmany }) hH hobstruction hlocalM hn
  obtain ⟨J, hJ, hJG, hrespoint, hselect⟩ := s.exists_selected_H hnonabelian
  let E' : Geometry D := { E with H := J }
  let f' : E'.ClosureFlag := {
    point_nonzero := s.flag.point_nonzero
    point_le_seed := s.flag.point_le_seed
    point_ne_seed := s.flag.point_ne_seed
    sylow_normalizes_point := s.flag.sylow_normalizes_point
    local_normalizes_seed := s.flag.local_normalizes_seed
    seed_irreducible := s.flag.seed_irreducible }
  have hsum (hK : E'.K = E'.L₁) : ∃ r : ℕ,
      Nonempty (ActionEquiv (Linear.Block.Multiplicity.action E' f' hK)
        (repeated (linearNatural E'.input.field 2) r)) := by
    let n := (s.naturalSeed hK).some
    let n' : f'.NaturalSeed hK := {
      groupEquiv := n.groupEquiv
      linearEquiv := n.linearEquiv
      intertwines := n.intertwines }
    exact f'.globalClosure_natural_sum n'
  have hab : IsMulCommutative E.W :=
    Linear.isMulCommutative_of_source E' m f hm.point.symm hm.threeSpace.symm f'
      s.cartan s.cartan_le s.component s.refinement s.no_triangle s.generation
      s.frattini_action s.core_commutator hsum hJ hJG hrespoint hselect s.sylow_normalizer
  have hcase : Chapter11.Source.ClassicalRefinementCase L E.L₁ E.K 1 E.input.field.degree := by
    cases s.refinement with
    | equal he => exact .equal (by simpa using he)
    | sl2 _ hn p hp hm => exact .sl2Prime rfl hn p hp hm
    | psl2 _ hn p hp hl hm hx => exact .psl2Prime rfl hn p hp hl hm hx
    | triangle _ _ ht => exact (s.no_triangle ht).elim
  have hK := Amalgam.linear_eq_of_abelian E m f hm
    ((le_conjugateSpanBy E.L₁ E.G₁).trans s.component_centralizes_point)
    hsplit s.cartan (s.point_torus.trans le_sup_left) hLi s.component s.local_model
    hcase hfixed (radicalCorank_of_preceding E s) hres hcomp horbit htrans hs hab
  exact hnonabelian hK hab


open Theory.SpecificGroups.SymplecticFour in
/-- Conditional symplectic exclusion, retaining the earlier C.1.32 MS-pair
classification on its actual original carrier. -/
theorem nonbinary_sp4_impossible_of_preceding_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : E.CartanPrecedingGeometry) (m : Symplectic.MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g⁻¹).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g⁻¹).toLinearMap)
    (hplane : ∀ x : V, (x : G) ∈ E.V₂ ↔
      (Symplectic.Terminal.markedProjection E m g x).toAdd ∈ plane E.input.field.Carrier)
    (hthree' : ∀ x : V, (x : G) ∈ E.V₃ ↔
      (Symplectic.Terminal.markedProjection E m g x).toAdd (.inr 0) = 0)
    (hcartan : Symplectic.PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g⁻¹).toMonoidHom)
    (hVX : ⁅V,E.X⁆ = V)
    (σ : MulAut (Sp E.input.field.Carrier))
    (hlocal₁ : (E.L₁.subgroupOf L).map
      (σ.toMonoidHom.comp (Symplectic.Terminal.RadicalGeometry.componentQuotient m)) = pointLocal)
    (hlocal₂ : (E.L₂.subgroupOf L).map
      (σ.toMonoidHom.comp (Symplectic.Terminal.RadicalGeometry.componentQuotient m)) = planeLocal)
    (hunique : Chapter11.Source.UniqueNoncentralComponent
      (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved₁ : ⁅V,E.L₁⁆ = E.V₃) (hmoved₂ : ⁅V,E.L₂⁆ = V)
    (hcontrol : normalizer (E.V₃ : Set G) ⊓ normalizer (E.L₁ : Set G) ≤ E.M)
    (hrecognition : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2) → ChapterC.IsSp4FourBlock L)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hNV : normalizer (V : Set G) ≤ E.M)
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1)
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v)
    (hcomp : E.Kz = E.K)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hobstruction : Chapter11.Source.WeakClosureObstruction (T : Subgroup G) V E.V₁ E.H)
    (hlocalM : @ChapterE.localM _ _ V D.elementary = E.input.field.degree)
    (hn : ChapterE.generationParameter E.H = 1)
    (hsplit : L ⊓ E.G₁ = (E.L₁ ⊔ L.pCoreIn 2) ⊔ E.X)
    (hLi : Chapter11.Source.ComponentIn E.M₁ E.L₁)
    (hres : pointResidual L E.z = E.L₁)
    (horbit : ∀ u ∈ E.V₁, u ≠ 1 → ∃ x ∈ L ⊓ E.G₁, (MulAut.conj x) E.z = u)
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞)) :
    False := by
  let F₀ : Nonabelian.MarkedFlag E :=
    ⟨.sp4 m.action, m.flag, m.point_eq, m.plane_eq, m.threeSpace_eq⟩
  have hnonabelian : E.K = E.L₁ → ¬ IsMulCommutative E.W :=
    Nonabelian.not_isMulCommutative_of_K_eq F₀ hfixed hNV hz hz1 htrans hcomp
      (Preliminary.seed_ti D { E.input with many := hmany }) hH hobstruction hlocalM hn
  have hab := Symplectic.abelian_of_preceding_and_ms_recognition E m g⁻¹
    hpoint hthree s.cartan hcartan s.flag.local_normalizes_seed s.flag.seed_irreducible
    (Preliminary.seed_ti D { E.input with many := hmany }) s.generation hVX
    (fun P he hPT hf => s.frattini_action P hPT he.symm hf) s.core_commutator
    (Amalgam.Even.Symplectic.pointCoordinates m g hpoint hplane hthree')
    σ hlocal₁ hlocal₂ hunique hmoved₁ hmoved₂ hcontrol
    (s.point_centralizer_escape hnonabelian) hrecognition
  have hcase : Chapter11.Source.ClassicalRefinementCase L E.L₁ E.K 1 E.input.field.degree := by
    cases s.refinement with
    | equal he => exact .equal (by simpa using he)
    | sl2 _ hn p hp hm => exact .sl2Prime rfl hn p hp hm
    | psl2 _ hn p hp hl hm hx => exact .psl2Prime rfl hn p hp hl hm hx
    | triangle _ _ ht => exact (s.no_triangle ht).elim
  have hK := Amalgam.symplectic_eq_of_abelian E m g hpoint hplane hthree'
    ((le_conjugateSpanBy E.L₁ E.G₁).trans s.component_centralizes_point)
    hsplit s.cartan (s.point_torus.trans le_sup_left) hLi s.component s.local_model
    hcase hfixed (radicalCorank_of_preceding E s) hres hcomp horbit htrans hs hab
  exact hnonabelian hK hab

open CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside

/-- Conditional G₂ exclusion from the literal preceding source geometry.
The R₁-Sylow witness is built on the original chosen quotient and its actual
full natural action; no projective replacement or terminal record is used. -/
theorem nonbinary_g2_impossible_of_preceding_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : LocalGeometry.InvariantFlag (.g2 m))
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Chapter11.Source.ClassicalRefinementCase L (f.Li 0)
      (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Chapter11.Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (LocalGeometry.sourceTL T L : Set G))
    (hcomponent : Chapter11.Source.UniqueNoncentralComponent
      (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1)) :
    False := by
  have _hmany := hmany
  exact ofFlag_g2_impossible_from_preceding S m f X z H h hcase he hNT hlinear
    h1132 hcontrol hunique hthree hline hcomponent

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
