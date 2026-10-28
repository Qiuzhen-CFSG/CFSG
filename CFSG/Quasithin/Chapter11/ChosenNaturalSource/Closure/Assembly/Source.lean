module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Assembly.Distance
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.OriginalDistance

/-!
# Source-specific endgame assembly from the critical distance argument

The distance-two replacement required by the symplectic closure is produced
from the nonabelian closure itself by the source-specific minimum-replacement
argument in `CharacteristicBlock.OriginalDistance`.  This adapter keeps the
literal selected H, flag preimages, Cartan and weak-closure inputs visible,
and then reuses the checked SL₃ and Sp₄ closure branches.  The older
`impossible_of_endgame_of_distance_two` theorem remains available for an
independent distance producer; this theorem is the source-specific route.

Source: Aschbacher--Smith 11.5.2--8, pp.779--784; MS93 (3.6), pp.870--872.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
open LocalGeometry
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
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

/-- The symplectic branch derives the critical distance-two replacement from
nonabelianness, so no external distance witness or C.1.32 classification is
needed at this source-specific boundary. -/
theorem sp4_impossible_of_endgame_of_source_distance
    (s : E.CartanPrecedingGeometry) (e : ShadowReduction.EndgameAt E)
    (m : Symplectic.MarkedFlag E)
    (hweak : Source.WeakClosureObstruction (T : Subgroup G) V E.V₁ E.H)
    (hsplit : L ⊓ E.G₁ = (E.L₁ ⊔ L.pCoreIn 2) ⊔ E.X)
    (hLi : Source.ComponentIn E.M₁ E.L₁)
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞))
    (hunique : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    : False := by
  let F₀ : Nonabelian.MarkedFlag E :=
    ⟨.sp4 m.action,m.flag,m.point_eq,m.plane_eq,m.threeSpace_eq⟩
  have hnonabelian := e.nonabelian_of_component_eq hweak
  have hmoved₁ : ⁅V,E.L₁⁆ = E.V₃ := by
    change ⁅V,localResidual L E.V₁⁆ = E.V₃
    rw [m.point_preimage,m.threeSpace_preimage]
    exact Normalizers.FixedSummand.Sp4.seed_first_commutator D E.input m.action m.flag
  have hp := m.point_coordinates
  have ht := m.three_coordinates
  have hab : IsMulCommutative E.W :=
    Symplectic.abelian_of_preceding E m (Sp4.alignment m.action)
      hp ht s.cartan (m.cartan_image (s.cartan.1.trans inf_le_left) hsplit)
      s.flag.local_normalizes_seed s.flag.seed_irreducible
      (Preliminary.seed_ti D E.input) s.generation
      (m.cartan_commutator s.cartan e.fixed_trivial)
      (fun P he hPT hf => s.frattini_action P hPT he.symm hf) s.core_commutator
      (Amalgam.Even.Symplectic.pointCoordinates m (Sp4.alignment m.action)⁻¹
        (by simpa only [inv_inv] using hp) m.plane_membership m.three_membership)
      (MulAut.conj (Sp4.alignment m.action)⁻¹)
      m.point_local_image m.plane_local_image hunique hmoved₁
      (m.plane_commutator e.fixed_trivial) (m.normalizer_control hunique)
      (s.point_centralizer_escape hnonabelian)
  have hK := Amalgam.symplectic_eq_of_abelian E m (Sp4.alignment m.action)⁻¹
    (by simpa only [inv_inv] using hp) m.plane_membership m.three_membership
    ((le_conjugateSpanBy E.L₁ E.G₁).trans s.component_centralizes_point)
    hsplit s.cartan (s.point_torus.trans le_sup_left) hLi s.component s.local_model
    e.refinement e.fixed_trivial (radicalCorank_of_preceding E s)
    (Nonabelian.PointModels.pointResidual_eq F₀ e.fixed_trivial e.point_mem e.point_ne_one)
    e.comparison (F₀.point_orbit e.fixed_trivial e.point_mem e.point_ne_one e.transitive)
    e.transitive hs hab
  exact hnonabelian hK hab

/-- The complete source-specific SL₃/Sp₄ endgame.  All preceding source
geometry and the selected weak-closure obstruction remain explicit. -/
theorem impossible_of_endgame_of_source_distance
    (s : E.CartanPrecedingGeometry) (e : ShadowReduction.EndgameAt E)
    (hweak : Source.WeakClosureObstruction (T : Subgroup G) V E.V₁ E.H)
    (hsplit : L ⊓ E.G₁ = (E.L₁ ⊔ L.pCoreIn 2) ⊔ E.X)
    (hLi : Source.ComponentIn E.M₁ E.L₁)
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞))
    (hunique : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    : False := by
  obtain ⟨a,f,hp,hpl,ht⟩ := s.marking
  cases a with
  | sl3 m =>
    exact sl3_impossible_of_endgame E s e m f ⟨hp.symm,hpl.symm,ht.symm⟩
      hweak hsplit hLi hs
  | sp4 a =>
    exact sp4_impossible_of_endgame_of_source_distance E s e ⟨a,f,hp,hpl,ht⟩
      hweak hsplit hLi hs hunique

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
