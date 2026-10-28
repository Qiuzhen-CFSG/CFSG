module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.FourMovementFixedFive
/-! The source four-group marks force the transfer-selected involution
outside the natural S6 action on its actual A6 component. This ambient form
uses only containment in the original two-group, index two, normalization by
the half subgroup, and a crossing element moving the four-group. It transports
the fixed D10 subgroup to the literal ambient relative centralizer.
Source: Aschbacher--Smith 2.4.29, printed p.546. -/
public section
open Subgroup
namespace AlternatingSix.ShadowLocal
variable {G : Type*} [Group G]

theorem five_dvd_centralizer_of_ambient_four_movement
    (K T : Subgroup G) (hTK : T ≤ normalizer (K:Set G))
    (hT : IsPGroup 2 T) (e : K ≃* A6)
    (F : Subgroup K) [IsKleinFour F] (hFT : F.map K.subtype ≤ T)
    (R : Subgroup T) (hR : R.index=2)
    (hRF : ∀r∈R, F.map (K.normalizerMonoidHom (inclusion hTK r)).toMonoidHom=F)
    (hx : ∃x:T, F.map (K.normalizerMonoidHom (inclusion hTK x)).toMonoidHom≠F)
    (i : T) (hi : i∉R) (hi2 : orderOf (i:G)=2) :
    5 ∣ Nat.card (K ⊓ centralizer ({(i:G)} : Set G) : Subgroup G) := by
  let F₀ := F.map e.toMonoidHom
  let : IsKleinFour F₀ := ⟨(Nat.card_congr (e.subgroupMap F).toEquiv).symm.trans IsKleinFour.card_four,
    (Monoid.exponent_eq_of_mulEquiv (e.subgroupMap F)).symm.trans IsKleinFour.exponent_two⟩
  have hmap (t:T) : F₀.map
      (MulAut.congr e (K.normalizerMonoidHom (inclusion hTK t))).toMonoidHom =
      (F.map (K.normalizerMonoidHom (inclusion hTK t)).toMonoidHom).map e.toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    exact congrArg e (congrArg (K.normalizerMonoidHom (inclusion hTK t)) (e.symm_apply_apply x))
  apply five_dvd_centralizer_of_four_movement K T hTK hT e F₀ R hR ?_ ?_ ?_ i hi hi2
  · rintro _ ⟨y,⟨a,ha,rfl⟩,rfl⟩
    let t : T := ⟨a,hFT (mem_map_of_mem K.subtype ha)⟩
    refine ⟨t,?_⟩
    change MulAut.congr e (K.normalizerMonoidHom (inclusion hTK t)) = MulAut.conj (e a)
    rw [←MulAut.congr_conj]
    congr 1
    ext b
    rfl
  · intro r hr
    rw [hmap,hRF r hr]
  · obtain ⟨x,hx⟩:=hx
    refine ⟨x,?_⟩
    rw [hmap]
    exact fun h=>hx (map_injective e.injective h)
end AlternatingSix.ShadowLocal
namespace AlternatingSix.ShadowLocal
open Subgroup
variable {G : Type*} [Group G]

theorem five_dvd_centralizer_of_four_normalizer
    (K T F : Subgroup G) (hTK : T ≤ normalizer (K:Set G))
    (hT : IsPGroup 2 T) (e : K ≃* A6) [IsKleinFour F]
    (hFK : F≤K) (hFT : F≤T)
    (R : Subgroup T) (hR : R.index=2)
    (hRF : R.map T.subtype ≤ normalizer (F:Set G))
    (hx : ∃x∈T, x∉normalizer (F:Set G))
    (i : T) (hi : i∉R) (hi2 : orderOf (i:G)=2) :
    5 ∣ Nat.card (K ⊓ centralizer ({(i:G)} : Set G) : Subgroup G) := by
  let F' := F.subgroupOf K
  let ef : F' ≃* F := subgroupOfEquivOfLe hFK
  let : IsKleinFour F' := ⟨(Nat.card_congr ef.toEquiv).trans IsKleinFour.card_four,
    (Monoid.exponent_eq_of_mulEquiv ef).trans IsKleinFour.exponent_two⟩
  have hFm : F'.map K.subtype=F := map_subgroupOf_eq_of_le hFK
  have hnorm (x:T) : F'.map
      (K.normalizerMonoidHom (inclusion hTK x)).toMonoidHom=F' ↔
      (x:G)∈normalizer (F:Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    constructor
    · intro h
      have he := congrArg (map K.subtype) h
      rw [map_map,hFm] at he
      have hc : K.subtype.comp (K.normalizerMonoidHom (inclusion hTK x)).toMonoidHom=
          (MulAut.conj (x:G)).toMonoidHom.comp K.subtype := rfl
      rwa [hc,←map_map,hFm] at he
    · intro h
      apply map_injective K.subtype_injective
      rw [map_map,hFm]
      change F'.map ((MulAut.conj (x:G)).toMonoidHom.comp K.subtype)=F
      rw [←map_map,hFm]
      exact h
  apply five_dvd_centralizer_of_ambient_four_movement K T hTK hT e F' (hFm.symm ▸ hFT)
    R hR ?_ ?_ i hi hi2
  · intro r hr
    exact (hnorm r).mpr (hRF (mem_map_of_mem T.subtype hr))
  · obtain ⟨x,hx,hxn⟩:=hx
    exact ⟨⟨x,hx⟩,fun hh=>hxn ((hnorm ⟨x,hx⟩).mp hh)⟩
end AlternatingSix.ShadowLocal
