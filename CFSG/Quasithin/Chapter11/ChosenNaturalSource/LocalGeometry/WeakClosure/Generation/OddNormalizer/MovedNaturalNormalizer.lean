module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedNaturalOrbit
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Bounds
public import Theory.GroupTheory.RankTwoDisjointAction
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The full normalizer of the original natural module in the moved J₄ case

The literal component quotient retains the order-64 module and its transitive
residual action. Every element of the full residual normalizer lifts to N_G(L),
so the original module commutes with each of its normalizer conjugates: both
lie in O₂(L), which centralizes V. Two distinct conjugates have trivial
intersection by transitivity, and would generate an elementary subgroup of
order 4096. The native J₄ two-rank bound excludes this.

Thus the residual and the original module have the same full normalizer.
The original module is normal in its radical and meets the radical's center
nontrivially. Transitivity then puts the entire unchanged module in that center.
No full Sylow containment or replacement of V by a larger orbit is used.

These results narrow the remaining inspection in Aschbacher--Smith 4.4.6--12,
printed pp.620--622, to the full normalizer of the particular pure elementary
64. They do not classify such normalizers or close the remaining J₄ exclusion.
Source applies them to the original failure and the literal Hall kernel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

private theorem transitive_invariant
    {Q : Type*} [Group Q] (X U B : Subgroup Q)
    (ht : ∀ u ∈ U, ∀ v ∈ U, u ≠ 1 → v ≠ 1 → ∃ x ∈ X, x * u * x⁻¹ = v)
    (hBU : B ≤ U) (hn : X ≤ normalizer (B : Set Q)) : B = ⊥ ∨ B = U := by
  by_cases hb : B = ⊥
  · exact Or.inl hb
  · obtain ⟨u,hu1⟩ := ne_bot_iff_exists_ne_one.mp hb
    exact Or.inr (le_antisymm hBU (by
      intro v hv
      by_cases hv1 : v = 1
      · exact hv1 ▸ B.one_mem
      · obtain ⟨x,hx,he⟩ := ht u (hBU u.property) v hv (fun h => hu1 (Subtype.ext h)) hv1
        exact he ▸ (mem_normalizer_iff.mp (hn hx) u).mp u.property))

private theorem large_transitive_commuting_module_normalized
    {Q : Type*} [Group Q] [Finite Q] (X U : Subgroup Q)
    (he : IsElementaryAbelian 2 U) (hc : Nat.card U = 64)
    (hr : primeRank 2 Q ≤ 11)
    (hcomm : ∀ g ∈ normalizer (X : Set Q),
      U.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set Q))
    (hn : X ≤ normalizer (U : Set Q))
    (ht : ∀ u ∈ U, ∀ v ∈ U, u ≠ 1 → v ≠ 1 → ∃ x ∈ X, x * u * x⁻¹ = v) :
    normalizer (X : Set Q) ≤ normalizer (U : Set Q) := by
  intro g hg
  let f := MulAut.conj g
  let W := U.map f.toMonoidHom
  have hX : X.map f.toMonoidHom = X := mem_normalizer_iff_map_conj_eq.mp hg
  have hWU : W ≤ centralizer (U : Set Q) := hcomm g hg
  have hnW : X ≤ normalizer (W : Set Q) := by
    rw [←hX]
    exact (map_mono hn).trans (U.le_normalizer_map f.toMonoidHom)
  have hnI : X ≤ normalizer ((U ⊓ W : Subgroup Q) : Set Q) :=
    (le_inf hn hnW).trans inf_normalizer_le_normalizer_inf
  have hne : U ⊓ W ≠ ⊥ := by
    intro hz
    let := he
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.map f.toMonoidHom
    have heJ : IsElementaryAbelian 2 (U ⊔ W : Subgroup Q) :=
      IsElementaryAbelian.sup_of_le_centralizer hWU
    have hb := (primeRank_le_iff_elementary_card_le Q).mp hr (U ⊔ W) heJ
    rw [card_sup_eq_mul_of_normalizes_of_disjoint U W
      (hWU.trans (Subgroup.centralizer_le_normalizer _)) (disjoint_iff.mpr hz),
      hc,show Nat.card W = 64 by
        change Nat.card (U.map f.toMonoidHom) = 64
        rw [card_map_of_injective f.injective,hc]] at hb
    norm_num at hb
  have hIU : U ⊓ W = U := (transitive_invariant X U (U ⊓ W) ht inf_le_left hnI).resolve_left hne
  have hUW : U ≤ W := hIU ▸ (inf_le_right : U ⊓ W ≤ W)
  have hEq : W = U := (eq_of_le_of_card_ge hUW (by
    change Nat.card (U.map f.toMonoidHom) ≤ Nat.card U
    rw [card_map_of_injective f.injective])).symm
  exact mem_normalizer_iff_map_conj_eq.mpr hEq



open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem moved_projected_module_commuting_conjugates
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    let q := QuotientGroup.mk' (center K)
    let X := (movedComponentSubgroup A (oddActorResidual L A) K).map q
    let U := (movedComponentSubgroup A V K).map q
    ∀ g ∈ normalizer (X : Set (K ⧸ center K)),
      U.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set (K ⧸ center K)) := by
  let q := QuotientGroup.mk' (center K)
  let E := movedComponentSubgroup A V K
  dsimp only
  intro g hg
  rw [moved_projected_residual_normalizer D S hA hodd hu K hFK] at hg
  obtain ⟨k,hk,rfl⟩ := hg
  have hVL : V ≤ L := ((actor_cover D S hA hodd).2.2.1.trans
    (pCoreIn_le 2 _)).trans ((oddActorResidual_le L A).trans inf_le_left)
  let := D.elementary
  have hVc : V ≤ L.pCoreIn 2 := (le_inf hVL
    (le_centralizer_iff_isMulCommutative.mpr inferInstance)).trans
      (centralizer_eq_core D S).le
  have hkN : k.val.val ∈ normalizer (L.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image L (pCore 2 L) hk
  have hE : E.map (MulAut.conj k).toMonoidHom ≤ centralizer (E : Set K) := by
    rintro _ ⟨v,hv,rfl⟩ w hw
    apply Subtype.ext
    apply Subtype.ext
    exact ((centralizer_eq_core D S).ge.trans inf_le_right)
      ((mem_normalizer_iff.mp hkN v.val.val).mp (hVc hv)) w.val.val hw
  rintro _ ⟨u,⟨v,hv,rfl⟩,rfl⟩ w ⟨w,hw,rfl⟩
  have hc := hE (mem_map_of_mem (MulAut.conj k).toMonoidHom hv) w hw
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
    map_mul,map_inv,MulEquiv.coe_toMonoidHom] using congrArg q hc

/-- The full residual normalizer equals the full normalizer of the unchanged
order-64 natural module, through the literal component central projection. -/
theorem moved_projected_module_normalizer
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hf : S.field.degree = 2) (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (ek : (K ⧸ center K) ≃* Janko4.Model) :
    let q := QuotientGroup.mk' (center K)
    let X := (movedComponentSubgroup A (oddActorResidual L A) K).map q
    let U := (movedComponentSubgroup A V K).map q
    normalizer (X : Set (K ⧸ center K)) = normalizer (U : Set (K ⧸ center K)) := by
  let q := QuotientGroup.mk' (center K)
  let X := (movedComponentSubgroup A (oddActorResidual L A) K).map q
  let U := (movedComponentSubgroup A V K).map q
  obtain ⟨hE,hne,_,hm⟩ := moved_projected_module D S hA hodd K hFK
  have hn : X ≤ normalizer (U : Set (K ⧸ center K)) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [commutator_comm,←hm]
  have hr : primeRank 2 (K ⧸ center K) ≤ 11 := by
    rw [primeRank_equiv 2 ek]
    exact Janko4.TwoRank.model_twoRank_le_eleven
  exact le_antisymm
    (large_transitive_commuting_module_normalized X U hE
      (moved_projected_module_card D S hA hodd K hFK hf e) hr
      (moved_projected_module_commuting_conjugates D S hA hodd hu K hFK) hn
      (moved_projected_module_transitive D S hA hodd K hFK hf e))
    (moved_projected_two_normalizer hu K hFK U hE.isPGroup hne hn)



/-- The original natural module is central in the radical of its full local
normalizer. The proof uses normality and residual transitivity, with no enlargement of V. -/
theorem moved_projected_module_central_radical
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hf : S.field.degree = 2) (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (ek : (K ⧸ center K) ≃* Janko4.Model) :
    let q := QuotientGroup.mk' (center K)
    let X := (movedComponentSubgroup A (oddActorResidual L A) K).map q
    let U := (movedComponentSubgroup A V K).map q
    U ≤ centerIn ((normalizer (X : Set (K ⧸ center K))).pCoreIn 2) := by
  let q := QuotientGroup.mk' (center K)
  let X := (movedComponentSubgroup A (oddActorResidual L A) K).map q
  let U := (movedComponentSubgroup A V K).map q
  let M := normalizer (X : Set (K ⧸ center K))
  let P := M.pCoreIn 2
  obtain ⟨hE,hne,hUX,_⟩ := moved_projected_module D S hA hodd K hFK
  have hnM : M ≤ normalizer (U : Set (K ⧸ center K)) :=
    (moved_projected_module_normalizer D S hA hodd hu K hFK hf e ek).le
  have hUP : U ≤ P := le_pCoreIn_of_normalizes hE.isPGroup
    ((hUX.trans (pCoreIn_le 2 X)).trans X.le_normalizer) hnM
  have hnP : X ≤ normalizer (P : Set (K ⧸ center K)) :=
    (X.le_normalizer.trans M.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hnB : X ≤ normalizer
      ((U ⊓ centralizer (P : Set (K ⧸ center K)) : Subgroup (K ⧸ center K)) : Set _) :=
    (le_inf (X.le_normalizer.trans hnM)
      (hnP.trans (normalizer_le_normalizer_centralizer P))).trans
      inf_normalizer_le_normalizer_inf
  have hneB : U ⊓ centralizer (P : Set (K ⧸ center K)) ≠ ⊥ := by
    have hnZ := inf_centerIn_ne_bot (isPGroup_pCoreIn 2 M) hne hUP
      ((pCoreIn_le 2 M).trans hnM)
    intro hz
    apply hnZ
    apply bot_unique
    exact (inf_le_inf_left U (show centerIn P ≤ centralizer (P : Set _) from
      inf_le_right)).trans (le_of_eq hz)
  have hBU := (transitive_invariant X U (U ⊓ centralizer (P : Set _))
    (moved_projected_module_transitive D S hA hodd K hFK hf e) inf_le_left hnB).resolve_left hneB
  exact le_inf hUP (hBU.ge.trans inf_le_right)



/-- The full native J₄ normalizer is the normalizer of the original pure
order-64 image, with the same component and quotient maps as the source. -/
theorem moved_janko_module_normalizer
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hf : S.field.degree = 2) (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (ek : (K ⧸ center K) ≃* Janko4.Model) :
    let q := QuotientGroup.mk' (center K)
    let X := ((movedComponentSubgroup A (oddActorResidual L A) K).map q).map ek.toMonoidHom
    let U := ((movedComponentSubgroup A V K).map q).map ek.toMonoidHom
    normalizer (X : Set Janko4.Model) = normalizer (U : Set Janko4.Model) := by
  have hn := congrArg (map ek.toMonoidHom)
    (moved_projected_module_normalizer D S hA hodd hu K hFK hf e ek)
  simpa only [map_equiv_normalizer_eq] using hn

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
