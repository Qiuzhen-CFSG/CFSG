module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.FiveLocal.Placement
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.FiveLocal.Coordinates
public import Theory.SpecificGroups.Alternating.DihedralFiveCentralizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The full ambient normalizer of the selected five-local component

Let L = E(C_G(F)) be the actual component supplied by 47.2(2). The
marked product N_G(F) = D₁₀ × L already embeds F⟨inverter⟩ in C_G(L).
Choose a dihedral ten-subgroup B inside L and its rotation subgroup E.
Since E centralizes the marked conjugate of z, 47.2(3) gives
|N_G(E)| = 100. The disjoint commuting subgroups B and C_G(L) both lie
in this normalizer. Thus |C_G(L)| ≤ 10, proving equality with the
original marked dihedral subgroup.

F is the characteristic Sylow five-subgroup of this centralizer, so
N_G(L) ≤ N_G(F). The reverse inclusion follows from the marked component
factor in N_G(F). Transporting that original product gives compatible
coordinates N_G(L) ≃ L × D₁₀ and the existing full ambient pair-fixer
calculation applies to the literal internal pair.

Only the placed component and the genuine two-central normalizer conclusion
of 47.2 are inputs. Their source producers remain responsible for 47.1–47.2;
no 47.5 pair, fixer, or orbit conclusion is assumed. The separate root
marking and final `FiveLocalPairs` assembly remain with their existing owner.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2 and the first paragraph
of the proof of 47.5, printed pp.261,263.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal
open PrimeNormalizers.FiveLocal
namespace EarlierFive
variable {G : Type*} [Group G] [Finite G] {D : Seed G} {t : G}

private def embed {F : Subgroup G} (W : RootFiveWitness D F) :
    (DihedralGroup 5 × alternatingGroup (Fin 5)) →* G :=
  (normalizer (F : Set G)).subtype.comp W.equiv.symm.toMonoidHom

private theorem embed_injective {F : Subgroup G} (W : RootFiveWitness D F) :
    Function.Injective (embed W) :=
  (normalizer (F : Set G)).subtype_injective.comp W.equiv.symm.injective

private theorem dihedral_centralizes {F : Subgroup G} (W : RootFiveWitness D F) :
    F ⊔ zpowers W.inverter ≤ centralizer (fiveComponent F : Set G) := by
  rw [← W.dihedral_factor, ← W.component_factor]
  rintro _ ⟨⟨d,a⟩, hd, rfl⟩
  apply mem_centralizer_iff.mpr
  rintro _ ⟨⟨e,b⟩, he, rfl⟩
  have ha : a = 1 := hd.2
  have he' : e = 1 := he.1
  subst a
  subst e
  exact (Commute.map (show Commute ((1,b) : DihedralGroup 5 × alternatingGroup (Fin 5))
    (d,1) from by
      change (1,b) * (d,1) = (d,1) * (1,b)
      simp) (embed W)).eq

private theorem dihedral_card {F : Subgroup G} (W : RootFiveWitness D F) :
    Nat.card (F ⊔ zpowers W.inverter : Subgroup G) = 10 := by
  rw [← W.dihedral_factor]
  change Nat.card (((⊤ : Subgroup (DihedralGroup 5)).prod
    (⊥ : Subgroup (alternatingGroup (Fin 5)))).map (embed W)) = 10
  rw [card_map_of_injective (embed_injective W),
    Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod]
  rw [card_top, card_bot, mul_one, DihedralGroup.nat_card]

private theorem component_disjoint_centralizer {F : Subgroup G} (W : RootFiveWitness D F) :
    Disjoint (fiveComponent F) (centralizer (fiveComponent F : Set G)) := by
  apply disjoint_def.mpr
  intro x hx hc
  have hz : (⟨x,hx⟩ : fiveComponent F) ∈ center (fiveComponent F) := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hc y y.property)
  have hh := (centerCongr (componentEquiv W) ⟨⟨x,hx⟩,hz⟩).property
  change componentEquiv W ⟨x,hx⟩ ∈ center (alternatingGroup (Fin 5)) at hh
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hh
  exact congrArg Subtype.val ((componentEquiv W).injective
    (hh.trans (componentEquiv W).map_one.symm))

private theorem five_normalizer_le_component_normalizer {F : Subgroup G}
    (W : RootFiveWitness D F) :
    normalizer (F : Set G) ≤ normalizer (fiveComponent F : Set G) := by
  let N := normalizer (F : Set G)
  let A := (⊥ : Subgroup (DihedralGroup 5)).prod
    (⊤ : Subgroup (alternatingGroup (Fin 5)))
  let K := A.map W.equiv.symm.toMonoidHom
  let : K.Normal := (inferInstance : A.Normal).map W.equiv.symm.toMonoidHom
    W.equiv.symm.surjective
  have h := K.le_normalizer_map N.subtype
  rw [K.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  have hK : K.map N.subtype = fiveComponent F := by
    rw [map_map]
    exact W.component_factor
  rwa [hK] at h

private theorem componentEquiv_symm_coe {F : Subgroup G} (W : RootFiveWitness D F)
    (a : alternatingGroup (Fin 5)) :
    ((componentEquiv W).symm a : G) = embed W (1,a) := by
  rfl

namespace PlacedComponent
variable (P : PlacedComponent D t)

/-- The marked dihedral subgroup is the full ambient component centralizer. -/
theorem centralizer_eq (T : TwoCentralFiveFamily D t) :
    centralizer (fiveComponent P.F : Set G) = P.F ⊔ zpowers P.witness.inverter := by
  let L := fiveComponent P.F
  let C := centralizer (L : Set G)
  obtain ⟨B, hBL, ⟨eB⟩⟩ := alternatingGroup.FiveLocalGeometry.exists_dihedral L
    (componentEquiv P.witness)
  obtain ⟨E, hE, hEB, hBN⟩ :=
    Theory.SpecificGroups.Alternating.DihedralFiveCentralizer.exists_five_subgroup B eB
  have hEz : FiveCentralizing D.z E :=
    ⟨hE, P.witness.inverter, P.witness.inverter_conj,
      hEB.trans (hBL.trans P.witness.component_le)⟩
  obtain ⟨eN⟩ := T.normalizer E hEz
  have hN : Nat.card (normalizer (E : Set G)) = 100 := by
    rw [Nat.card_congr eN.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
  have hCN : C ≤ normalizer (E : Set G) :=
    (centralizer_le (hEB.trans hBL)).trans (centralizer_le_normalizer _)
  have hd : Disjoint B C := (component_disjoint_centralizer P.witness).mono_left hBL
  let f : B × C → normalizer (E : Set G) :=
    fun x => ⟨x.1 * x.2, mul_mem (hBN x.1.property) (hCN x.2.property)⟩
  have hf : Function.Injective f := fun _ _ h =>
    mul_injective_of_disjoint hd (congrArg Subtype.val h)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_congr eB.toEquiv, DihedralGroup.nat_card, hN] at hc
  apply (eq_of_le_of_card_ge (dihedral_centralizes P.witness) ?_).symm
  rw [dihedral_card P.witness]
  change Nat.card C ≤ 10
  omega

/-- The normalizer preserves the original order-five subgroup: it is the
characteristic Sylow subgroup of the component's dihedral centralizer. -/
theorem normalizer_eq (T : TwoCentralFiveFamily D t) :
    normalizer (fiveComponent P.F : Set G) = normalizer (P.F : Set G) := by
  apply le_antisymm _ (five_normalizer_le_component_normalizer P.witness)
  let C := centralizer (fiveComponent P.F : Set G)
  have hC : Nat.card C = 10 := by
    rw [show C = P.F ⊔ zpowers P.witness.inverter from P.centralizer_eq T,
      dihedral_card P.witness]
  have hFC : P.F ≤ C := le_sup_left.trans (dihedral_centralizes P.witness)
  have hF : Nat.card (P.F.subgroupOf C) = 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hFC).toEquiv, P.five.1]
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let S : Sylow 5 C := Sylow.ofCard (P.F.subgroupOf C) (by rw [hF, hC]; decide +kernel)
  have hi : (P.F.subgroupOf C).index = 2 := by
    have h := (P.F.subgroupOf C).card_mul_index
    rw [hF, hC] at h
    omega
  let : (P.F.subgroupOf C).Characteristic :=
    S.characteristic_of_normal (normal_of_index_eq_two hi)
  have hn := normalizer_le_normalizer_characteristic_image C (P.F.subgroupOf C)
  rw [map_subgroupOf_eq_of_le hFC] at hn
  exact (normalizer_le_normalizer_centralizer (fiveComponent P.F)).trans hn

/-- Full normalizer coordinates, retaining the witness's original dihedral factor. -/
noncomputable def normalizerEquiv (T : TwoCentralFiveFamily D t) :
    normalizer (fiveComponent P.F : Set G) ≃* (fiveComponent P.F × DihedralGroup 5) :=
  (MulEquiv.subgroupCongr (P.normalizer_eq T)).trans
    (P.witness.equiv.trans (MulEquiv.prodComm.trans
      ((componentEquiv P.witness).symm.prodCongr (MulEquiv.refl _))))

theorem normalizerEquiv_on_component (T : TwoCentralFiveFamily D t)
    (l : fiveComponent P.F) :
    P.normalizerEquiv T (inclusion (fiveComponent P.F).le_normalizer l) = (l,1) := by
  let a := componentEquiv P.witness l
  have he : embed P.witness (1,a) = (l : G) := by
    rw [← componentEquiv_symm_coe, MulEquiv.symm_apply_apply]
  have hn : P.witness.equiv.symm (1,a) =
      (MulEquiv.subgroupCongr (P.normalizer_eq T))
        (inclusion (fiveComponent P.F).le_normalizer l) := Subtype.ext he
  have hh := congrArg P.witness.equiv hn
  rw [MulEquiv.apply_symm_apply] at hh
  change ((componentEquiv P.witness).symm
    (P.witness.equiv ((MulEquiv.subgroupCongr (P.normalizer_eq T))
      (inclusion (fiveComponent P.F).le_normalizer l))).2,
    (P.witness.equiv ((MulEquiv.subgroupCongr (P.normalizer_eq T))
      (inclusion (fiveComponent P.F).le_normalizer l))).1) = (l,1)
  rw [← hh]
  simp only [a, MulEquiv.symm_apply_apply]

/-- Coordinates consumed by `ComponentCoordinates.fiveFixerEquiv` and `pairs`.
The component, its marking, and X's inclusion are literally those of P. -/
noncomputable def coordinates (T : TwoCentralFiveFamily D t) : ComponentCoordinates D where
  L := fiveComponent P.F
  equiv := componentEquiv P.witness
  X_le := P.X_le
  normalizerEquiv := P.normalizerEquiv T
  on_component := P.normalizerEquiv_on_component T

/-- The new coordinates preserve the original marked dihedral factor. -/
theorem normalizerEquiv_on_dihedral (T : TwoCentralFiveFamily D t) (d : DihedralGroup 5) :
    P.normalizerEquiv T ((MulEquiv.subgroupCongr (P.normalizer_eq T).symm)
      (P.witness.equiv.symm (d,1))) = (1,d) := by
  change ((componentEquiv P.witness).symm
    (P.witness.equiv (P.witness.equiv.symm (d,1))).2,
    (P.witness.equiv (P.witness.equiv.symm (d,1))).1) = (1,d)
  rw [MulEquiv.apply_symm_apply]
  simp

open Theory.GroupTheory.GraphUniquenessSystem

/-- Application to the actual ambient pair fixer from the independent internal pair. -/
noncomputable def fiveFixerEquiv (T : TwoCentralFiveFamily D t)
    (I : InternalPairs D (fiveComponent P.F)) :
    edgeFixer G D.base I.five ≃* (Multiplicative (ZMod 2) × DihedralGroup 5) :=
  (P.coordinates T).fiveFixerEquiv I

/-- The pair fixer lies in the original order-five normalizer. -/
theorem fiveFixer_le_normalizer (T : TwoCentralFiveFamily D t)
    (I : InternalPairs D (fiveComponent P.F)) :
    edgeFixer G D.base I.five ≤ normalizer (P.F : Set G) := by
  rw [← P.normalizer_eq T]
  exact (P.coordinates T).fixer_le_normalizer I

end PlacedComponent
end EarlierFive
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal
