module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.SourceGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.NaturalAxis
/-!
# Coordinates of the literal first residual and prescribed Sylow

The original marked product identifies each first factor inclusion with
its coordinate axis. Residual functoriality preserves that actual map.
The prescribed Sylow has two Sylow coordinate projections and the exact
product fixed space. Swapping the two original markings constructs the
second source instance without changing its factors.
Source: Aschbacher–Smith B.6.9–10, pp.115–117.
-/
@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
open QuasisimpleSource SourceInduction
variable {H : Type*} [Group H] [Finite H]
variable (F : BinaryField)
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F.Carrier
local notation "V" => Fin 2 → F.Carrier
local notation "N" => linearNatural F 2

theorem layer_fixedSpace_product
    (Y : Subgroup H) (e : Y ≃* D × D)
    (ρ : Representation (ZMod 2) H (V × V))
    (he : ∀ g : Y, ∀ v, ρ (g:H) v = SL2NaturalOffenders.naturalPair (F := F.Carrier) (e g) v)
    (S : Subgroup H) (P₀ : Sylow 2 Y) (hS : (P₀ : Subgroup Y).map Y.subtype = S) :
    ∃ P Q : Sylow 2 D, fixedSpace ρ S = (fixedSpace N (P:Subgroup D)).prod (fixedSpace N (Q:Subgroup D)) := by
  let R := P₀.mapSurjective (f := e.toMonoidHom) e.surjective
  let P := R.mapSurjective (f := MonoidHom.fst D D) (fun x => ⟨(x,1),rfl⟩)
  let Q := R.mapSurjective (f := MonoidHom.snd D D) (fun x => ⟨(1,x),rfl⟩)
  refine ⟨P,Q,?_⟩
  rw [←hS]
  ext v
  constructor
  · intro hv
    constructor
    · intro a
      obtain ⟨r,⟨g,hg,hr⟩,ha⟩ := a.property
      have hh := hv ⟨g,mem_map_of_mem Y.subtype hg⟩
      change ρ (g:H) v = v at hh
      rw [he] at hh
      have h := congrArg Prod.fst hh
      change N (e g).1 v.1 = v.1 at h
      change N (a:D) v.1 = v.1
      rw [←ha,←hr]
      exact h
    · intro a
      obtain ⟨r,⟨g,hg,hr⟩,ha⟩ := a.property
      have hh := hv ⟨g,mem_map_of_mem Y.subtype hg⟩
      change ρ (g:H) v = v at hh
      rw [he] at hh
      have h := congrArg Prod.snd hh
      change N (e g).2 v.2 = v.2 at h
      change N (a:D) v.2 = v.2
      rw [←ha,←hr]
      exact h
  · intro hv a
    obtain ⟨g,hg,hga⟩ := a.property
    change ρ a v = v
    rw [←hga]
    change ρ (g:H) v = v
    rw [he]
    exact Prod.ext (hv.1 ⟨(e g).1,mem_map_of_mem (MonoidHom.fst D D) (mem_map_of_mem e.toMonoidHom hg)⟩)
      (hv.2 ⟨(e g).2,mem_map_of_mem (MonoidHom.snd D D) (mem_map_of_mem e.toMonoidHom hg)⟩)

variable {G : Type*} [Group G] [Finite G]
theorem first_residual_image_of_marking
    (q : G →* H) (hq : Function.Surjective q) (Y : Subgroup H)
    (A : Subgroup Y) (e : Y ≃* D × D)
    (hA : ((⊤ : Subgroup D).prod ⊥).map e.symm.toMonoidHom = A) :
    (factorResidual q Y A).map q = (pResidual 2 D).map
      (Y.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inl D D))) := by
  let j := Y.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inl D D))
  have haxis : (⊤ : Subgroup D).map (MonoidHom.inl D D) = (⊤ : Subgroup D).prod ⊥ := by
    ext x
    constructor
    · rintro ⟨a,_,rfl⟩
      exact ⟨mem_top _,mem_bot.mpr rfl⟩
    · rintro ⟨_,h⟩
      exact ⟨x.1,mem_top _,Prod.ext rfl h.symm⟩
  have ht : (⊤ : Subgroup D).map j = A.map Y.subtype := by
    rw [show j = Y.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inl D D)) from rfl,
      ←map_map,←map_map,haxis,hA]
  have hh := map_embedded_pResidual 2 (⊤ : Subgroup D) j
  have hr : (pResidual 2 (⊤ : Subgroup D)).map (⊤ : Subgroup D).subtype = pResidual 2 D :=
    map_pResidual_of_surjective 2 _ (fun x => ⟨⟨x,mem_top _⟩,rfl⟩)
  rw [hr,ht] at hh
  rw [factorResidual_image q hq,map_embedded_pResidual]
  exact hh.symm

variable {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
  {D₀ M : Type*} [Group D₀] [AddCommGroup M] [Module (ZMod 2) M]
  {σ : Representation (ZMod 2) H X} {d : SourceTwoFactorCase σ}
  {τ : Representation (ZMod 2) D₀ M}
noncomputable def sourceSwap (d : SourceTwoFactorCase σ) : SourceTwoFactorCase σ where
  first := d.second
  second := d.first
  product := d.product.swap
  firstSpace := d.secondSpace
  secondSpace := d.firstSpace
  decomposition := d.decomposition.symm
  firstCase := d.secondCase
  secondCase := d.firstCase

noncomputable def markedSwap (c : d.MarkedProduct τ) : (sourceSwap d).MarkedProduct τ where
  action := {
    groupEquiv := c.action.groupEquiv.trans ((MulEquiv.prodComm : (D₀ × D₀) ≃* (D₀ × D₀)))
    linearEquiv := c.action.linearEquiv.trans (LinearEquiv.prodComm (ZMod 2) M M)
    intertwines := by
      intro g v
      have hh := congrArg Prod.swap (c.action.intertwines g v)
      exact hh }
  first_eq := by
    change ((⊤ : Subgroup D₀).prod (⊥ : Subgroup D₀)).map
      (c.action.groupEquiv.trans ((MulEquiv.prodComm : (D₀ × D₀) ≃* (D₀ × D₀)))).symm.toMonoidHom = d.second
    change (((⊤ : Subgroup D₀).prod (⊥ : Subgroup D₀))).map (c.action.groupEquiv.symm.toMonoidHom.comp ((MulEquiv.prodComm : (D₀ × D₀) ≃* (D₀ × D₀))).toMonoidHom) = _
    rw [←map_map]
    have hswap : ((⊤ : Subgroup D₀).prod (⊥ : Subgroup D₀)).map
        ((MulEquiv.prodComm : (D₀ × D₀) ≃* (D₀ × D₀))).toMonoidHom = (⊥ : Subgroup D₀).prod ⊤ := by
      ext x
      constructor
      · rintro ⟨v,hv,rfl⟩
        exact ⟨hv.2,hv.1⟩
      · intro hx
        exact ⟨x.swap,⟨hx.2,hx.1⟩,rfl⟩
    rw [hswap,c.second_eq]
  second_eq := by
    change ((⊥ : Subgroup D₀).prod (⊤ : Subgroup D₀)).map
      (c.action.groupEquiv.trans ((MulEquiv.prodComm : (D₀ × D₀) ≃* (D₀ × D₀)))).symm.toMonoidHom = d.first
    change (((⊥ : Subgroup D₀).prod (⊤ : Subgroup D₀))).map (c.action.groupEquiv.symm.toMonoidHom.comp ((MulEquiv.prodComm : (D₀ × D₀) ≃* (D₀ × D₀))).toMonoidHom) = _
    rw [←map_map]
    have hswap : ((⊥ : Subgroup D₀).prod (⊤ : Subgroup D₀)).map
        ((MulEquiv.prodComm : (D₀ × D₀) ≃* (D₀ × D₀))).toMonoidHom = (⊤ : Subgroup D₀).prod ⊥ := by
      ext x
      constructor
      · rintro ⟨v,hv,rfl⟩
        exact ⟨hv.2,hv.1⟩
      · intro hx
        exact ⟨x.swap,⟨hx.2,hx.1⟩,rfl⟩
    rw [hswap,c.first_eq]
end CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
