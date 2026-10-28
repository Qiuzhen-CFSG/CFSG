module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.CoveredCase.ActorNormality
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Omega
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.Transport
public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.CoverStructure

/-!
# Valid omega facts and obstructions in the covered Suzuki branch

The source permits the nontrivial Suzuki cover in the first paragraph of
Proposition 16.5.1. Its precise cover inputs do prove that V is elementary
and contains the external omega subgroup U. They also place the cover center
in U_C. However, the index-eight omega quotient and Z(T_L)=Z(L) prove that
U_L is not central in T_L, so the actual component action on V is nontrivial.
The imported actor-normality argument shows that even `Geometry`, without
`LocalAction.image_eq`, conflicts with these covered Sylow data.

Quotienting V by the cover center cannot retain a conjugator taking U_C to
U: faithfulness makes U disjoint from U_C, so such a conjugator does not
normalize the nontrivial cover center. The earlier 16.2.11 exclusion also
cannot be used here: its element of T outside N_G(L) contradicts the present
standard setup T ≤ N_G(L).

These conditional constructions and diagnostics are retained independently
of the ambient exclusion in `CoveredCase.Exclusion`. That exclusion uses
the genuine whole-Sylow displacement bound and the TI normalizer action.
No geometry or desired center exclusion is assumed, and no later Bender
result is fed back into 16.4.10.

Source: Aschbacher–Smith, 16.1.2, printed p.1170; 16.4.10–11 and 16.5.1,
printed pp.1193–1195; I.2.2(4), printed p.409, manuscript of 1 March 2004.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.CoveredCase
open Subgroup CoverAndSylowElimination

variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}

/-- The elementary component omega subgroup is not central in T_L: otherwise
Z(T_L)=Z(L) would make its index over the component center one, not eight. -/
theorem omega_not_central (d : SuzukiCoverInput T L) :
    ¬ omegaOneAmbient (componentSylow T L) ≤ centralizer (componentSylow T L : Set G) := by
  intro h
  have hle : sylowOmega T L ≤ componentCenter L := by
    rw [← d.center_sylow]
    intro x hx
    refine ⟨⟨x, sylowOmega_le hx⟩, ?_, rfl⟩
    exact mem_center_iff.mpr fun a => Subtype.ext (h hx a a.property)
  have he := le_antisymm hle d.omega_structure.2.1
  have hi := d.omega_structure.2.2
  rw [he, relIndex_self] at hi
  omega

/-- The actual elementary cover center lies in the commuting omega subgroup. -/
theorem center_le_commuting_omega (d : SuzukiCoverInput T L) :
    componentCenter L ≤ omegaOneAmbient (commutingSylow T L) := by
  let := d.center_elementary
  rintro x ⟨x, hx, rfl⟩
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl
  · refine ⟨(d.center_le_sylow (mem_map_of_mem L.subtype hx)).1, ?_⟩
    intro y hy
    exact congrArg L.subtype (mem_center_iff.mp hx ⟨y, hy⟩)
  · exact congrArg L.subtype (elemPow_eq_one_of_isElementaryAbelian x hx)

/-- A conjugator carrying U_C to the faithful external U cannot preserve a
nontrivial component center. Thus it cannot act on the quotient by that center. -/
theorem mover_not_normalizes_center {R : Subgroup G} {a : G}
    (d : SuzukiCoverInput T L) (hne : center L ≠ ⊥)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hmover : (omegaOneAmbient (commutingSylow T L)).conjBy a = omegaOneAmbient R) :
    a ∉ normalizer (componentCenter L : Set G) := by
  intro ha
  have hZ := center_le_commuting_omega d
  have hZR : componentCenter L ≤ omegaOneAmbient R := by
    have hh := map_mono (f := (MulAut.conj a).toMonoidHom) hZ
    change (componentCenter L).conjBy a ≤
      (omegaOneAmbient (commutingSylow T L)).conjBy a at hh
    have he : (componentCenter L).conjBy a = componentCenter L :=
      mem_normalizer_iff_map_conj_eq.mp ha
    rwa [he, hmover] at hh
  have hbot : componentCenter L = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact mem_bot.mpr (disjoint_def.mp hfaith
      (omegaOneAmbient_le _ (hZR hx))
      ((omegaOneAmbient_le _ (hZ hx)).2))
  apply hne
  apply le_bot_iff.mp
  intro x hx
  have hh : (x : G) ∈ componentCenter L := mem_map_of_mem L.subtype hx
  rw [hbot] at hh
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp hh))

variable [Finite G]

/-- The nonnormal-component inputs of the earlier cover exclusion are incompatible
with this standard setup. In particular they cannot be supplied to reuse 16.2.11 here. -/
theorem standard_excludes_earlier {z u : G} (h : StandardSetup T z L) :
    ¬ EarlierConclusions T z u L := by
  intro he
  exact he.u_not_normalizer (h.sylow_normalizes he.u_mem)

/-- The valid first-paragraph omega configuration follows from the genuine cover
and ambient inputs. This does not construct an actor or impose actor normality. -/
theorem omega_configuration {z g : G} {R : Subgroup G}
    (h : IntersectionSetup T z L g R) (d : SuzukiCoverInput T L)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hdelta : omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L)
    (hfaith : Disjoint R (centralizer (L : Set G))) :
    omegaOneAmbient R ≤ benderSpace T L ∧
      IsElementaryAbelian 2 (benderSpace T L) ∧
      componentCenter L ≤ omegaOneAmbient (commutingSylow T L) := by
  let : IsElementaryAbelian 2 (omegaOneAmbient (componentSylow T L)) :=
    d.omega_structure.1
  have hlift : InvolutionLifting L := ⟨d.center_elementary, d.involutions_lift⟩
  let := commuting_omega_elementary h hR htransport hlift hdelta hfaith
  exact ⟨omega_le_space h hlift hdelta, space_elementary_of_factors,
    center_le_commuting_omega d⟩

/-- The actual action of T_L on V is nontrivial in the covered configuration.
This uses the ambient Sylow normalization, with no torus-action premise. -/
theorem component_image_ne_bot {z : G} (h : StandardSetup T z L)
    (d : SuzukiCoverInput T L) :
    inducedActor (benderSpace T L) (componentSylow T L) ≠ ⊥ := by
  intro he
  apply omega_not_central d
  intro u hu a ha
  have hnorm := (sylow_normalizes_factors h).1
  let aN : normalizer (benderSpace T L : Set G) := ⟨a, hnorm ha.1⟩
  have hm : (benderSpace T L).normalizerMonoidHom.rangeRestrict aN ∈
      inducedActor (benderSpace T L) (componentSylow T L) := ⟨aN, ha, rfl⟩
  rw [he] at hm
  have hev := congrArg (fun b : ActionImage (benderSpace T L) =>
    (b : MulAut (benderSpace T L))
      ⟨u, (show omegaOneAmbient (componentSylow T L) ≤ benderSpace T L from le_sup_right) hu⟩)
    (mem_bot.mp hm)
  have hev' : a * u * a⁻¹ = u := congrArg Subtype.val hev
  exact mul_inv_eq_iff_eq_mul.mp hev'


end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.CoveredCase
