module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldEvenSquareObstruction
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldEvenAffine
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.EvenGeometry.SylowAffineTransport

/-!
# The original escaping point excludes the even affine normalizer

The original opposite plane has a square outside it by the faithful B.5
source argument. The marked even affine model carries this same plane,
its original Sylow, and its intersection with U to the native square
calculation. These two conclusions contradict one another.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

public theorem original_tripleSix_escaping_sylow_not_le_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G)) :
    ¬(T : Subgroup G)≤K := by
  intro hTK
  obtain ⟨W,hWe,hWc,hWT,hTW,hIW,x,hx,hxW⟩ :=
    original_tripleSix_escaping_even_square_obstruction h structural D a t ht heven hout hTK
  obtain ⟨E,_,_,hEU⟩ :=
    original_tripleSix_escaping_even_affine h structural D a t ht heven hout hTK
  let V := Multiplicative hexacode
  let A := V ⋊[hexAffineAction.comp hexSign.ker.subtype] HexEvenAutomorphisms
  let S : Sylow 2 A := (T.subtype hTK).mapSurjective (f := E.toMonoidHom) E.surjective
  let W₀ := (W.subgroupOf K).map E.toMonoidHom
  have hWK : W≤K := hWT.trans hTK
  let := hWe
  let : IsElementaryAbelian 2 (W.subgroupOf K) := IsElementaryAbelian.subgroupOf hWK
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.map _
  have hWS : W₀≤(S : Subgroup A) := map_mono (subgroupOf_mono K hWT)
  have hSW : (S : Subgroup A)≤normalizer (W₀ : Set A) := by
    apply (map_mono (show (T : Subgroup G).subgroupOf K≤
      normalizer (W.subgroupOf K : Set K) from ?_)).trans ((W.subgroupOf K).le_normalizer_map E.toMonoidHom)
    rw [←subgroupOf_normalizer_eq hWK]
    exact subgroupOf_mono K hTW
  have hW₀ : Nat.card W₀=64 := by
    rw [card_map_of_injective E.injective,Nat.card_congr (subgroupOfEquivOfLe hWK).toEquiv]
    exact hWc
  have hI₀ : Nat.card (W₀⊓(SemidirectProduct.inl : V→*A).range : Subgroup A)=16 := by
    change Nat.card ((W.subgroupOf K).map E.toMonoidHom⊓
      (SemidirectProduct.inl : V→*A).range : Subgroup A)=16
    rw [←hEU,←Subgroup.map_inf _ _ _ E.injective,card_map_of_injective E.injective]
    change Nat.card ((W⊓U).subgroupOf K)=16
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hWK)).toEquiv,inf_comm]
    exact hIW
  have hs := ChapterK.Alternating.HexacodeOffenders.EvenGeometry.SylowModel.affine_sylow_squares_mem
    S W₀ hWS hSW hW₀ hI₀
  have hxS : E (⟨x,hTK hx⟩:K)∈(S : Subgroup A) := mem_map.mpr ⟨⟨x,hTK hx⟩,hx,rfl⟩
  have hh := hs _ hxS
  rw [←map_pow] at hh
  have hx₂ : (⟨x,hTK hx⟩:K)^2∈W.subgroupOf K :=
    (mem_map_iff_mem (f := E.toMonoidHom) E.injective).mp hh
  exact hxW hx₂

end CFSG.Quasithin.Chapter12.Section07
