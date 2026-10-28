module
public import Theory.SpecificGroups.PSL2.ThompsonBorel
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Theory.SpecificGroups.SymmetricFive.SylowNormalizer
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters

/-!
# The exceptional L₂(4) Thompson actor

The actual isomorphisms L₂(4) ≃ A₅ and Aut(A₅) ≃ S₅ show that a two-subgroup
containing the inner Sylow four-group and an outer actor is a Sylow subgroup
of S₅. Its normalizer is itself. Thus a two-subgroup J normalizing L₂(4) and
containing its Sylow has two possibilities: its inner action lets the Borel
normalize J, or every odd-prime group normalizing both J and the component
centralizes the component. The latter is the model input for the original
prime actor of source 15.1.21(ii); no Thompson normalization is assumed.
Source: Aschbacher--Smith 15.1.21(ii), printed p.1098, and the existing
exceptional-isomorphism and symmetric Sylow-normalizer proofs.
-/

public section
open Subgroup
namespace Theory.PSL2.OrdinaryBorel

/-- A two-subgroup containing a Sylow inner four and an outer automorphism
is a self-normalizing Sylow subgroup of Aut(L₂(4)). -/
theorem four_outer_sylow_self_normalizing
    (P : Sylow 2 (BinaryGroup 2)) (D : Subgroup (MulAut (BinaryGroup 2)))
    (hD : IsPGroup 2 D) (hPD : (P : Subgroup (BinaryGroup 2)).map MulAut.conj ≤ D)
    (hout : ¬ D ≤ inner (BinaryField 2)) : normalizer (D:Set _) = D := by
  let e : MulAut (BinaryGroup 2) ≃* Equiv.Perm (Fin 5) :=
    (MulAut.congr Atlas.Comparisons.Exceptional.psl2FourEquivAlt5).trans
      Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv.symm
  have hcard : Nat.card (MulAut (BinaryGroup 2))=120 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hinj : Function.Injective (MulAut.conj : BinaryGroup 2 →* MulAut (BinaryGroup 2)) :=
    MulAut.conj_injective_of_center_eq_bot BenderSuzuki.ZD.Linear.psl2_center_eq_bot
  have hp : Nat.card ((P : Subgroup (BinaryGroup 2)).map MulAut.conj)=4 := by
    rw [card_map_of_injective hinj,sylow_card P,GaloisField.card 2 2 (by decide)]
    decide
  have hlt : (P : Subgroup (BinaryGroup 2)).map MulAut.conj < D := by
    refine lt_of_le_of_ne hPD ?_
    intro he
    apply hout
    rw [←he]
    exact map_le_range _ _
  have hlo : 4 < Nat.card D := by
    by_contra hh
    have he := eq_of_le_of_card_ge hPD (by omega)
    exact hlt.ne he
  obtain ⟨k,hk⟩ := hD.exists_card_eq
  have hc : Nat.Coprime (Nat.card D) 15 := hk ▸ (by decide : Nat.Coprime 2 15).pow_left k
  have hd : Nat.card D ∣ 8 := hc.dvd_of_dvd_mul_right (by
    simpa only [hcard] using D.card_subgroup_dvd_card)
  have he : Nat.card D=8 := by
    obtain ⟨m, hm⟩ := hd
    have hmpos : 0 < m := by nlinarith
    have hmone : m = 1 := by nlinarith
    simpa only [hmone, mul_one] using hm.symm
  let R : Sylow 2 (MulAut (BinaryGroup 2)) := Sylow.ofCard D (by rw [he,hcard]; decide +kernel)
  let Q := R.mapSurjective (f:=e.toMonoidHom) e.surjective
  apply map_injective (f:=e.toMonoidHom) e.injective
  have hn := map_equiv_normalizer_eq D e
  rw [hn]
  exact Theory.SpecificGroups.SymmetricFive.SylowNormalizer.sylow_normalizer_eq_self Q

variable {G : Type*} [_root_.Group G] [Finite G]

/-- The inner-image Borel route or the outer-image odd-actor centralization route. -/
theorem four_borel_or_odd_actor_centralizes
    (L J : Subgroup G) (hJ : IsPGroup 2 J) (hJL : J ≤ normalizer (L : Set G))
    (P : Sylow 2 L) (hPJ : (P : Subgroup L).map L.subtype ≤ J)
    (e : L ≃* BinaryGroup 2) :
    (normalizer (P : Set L)).map L.subtype ≤ normalizer (J : Set G) ∨
    ∀ (p : ℕ), Nat.Coprime p 2 → ∀ (Y : Subgroup G), IsPGroup p Y →
      Y ≤ normalizer (L : Set G) → Y ≤ normalizer (J : Set G) →
      Y ≤ centralizer (L : Set G) := by
  let N := normalizer (L : Set G)
  let f : N →* MulAut (BinaryGroup 2) :=
    (MulAut.congr e).toMonoidHom.comp L.normalizerMonoidHom
  let J0 := J.subgroupOf N
  let D := J0.map f
  have hD : IsPGroup 2 D := (hJ.comap_subtype (K:=N)).map f
  by_cases hi : D ≤ inner (BinaryField 2)
  · left
    apply sylowNormalizer_le_normalizer_of_inner_action L J hJ hJL P hPJ
    intro j
    have hj : f ⟨j,hJL j.property⟩ ∈ D := mem_map_of_mem f j.property
    obtain ⟨l,hl⟩ := hi hj
    exact (MulAut.congr_inner_iff e _).mp ⟨l,hl.symm⟩
  · right
    let R := P.mapSurjective (f:=e.toMonoidHom) e.surjective
    have hPD : (R : Subgroup (BinaryGroup 2)).map MulAut.conj ≤ D := by
      rintro a ⟨r,⟨l,hl,rfl⟩,rfl⟩
      have hlJ := hPJ (mem_map_of_mem L.subtype hl)
      refine ⟨⟨l,hJL hlJ⟩,hlJ,?_⟩
      ext y
      change e (l*e.symm y*l⁻¹)=e l*y*(e l)⁻¹
      rw [map_mul,map_mul,map_inv,e.apply_symm_apply]
    have hN := four_outer_sylow_self_normalizing R D hD hPD hi
    intro p hp Y hY hYL hYJ
    let Y0 := Y.subgroupOf N
    have hYN : Y0 ≤ normalizer (J0 : Set N) := by
      rw [←subgroupOf_normalizer_eq hJL]
      exact subgroupOf_mono N hYJ
    have hmap : Y0.map f ≤ D := by
      rw [←hN]
      exact (map_mono hYN).trans (le_normalizer_map f)
    have hdis := ((hY.comap_subtype (K:=N)).map f).disjoint_of_coprime hD hp
    have hbot : Y0.map f=⊥ := by
      apply bot_unique
      rw [←hdis.eq_bot]
      exact le_inf le_rfl hmap
    intro y hy
    have hyf : f ⟨y,hYL hy⟩=1 := mem_bot.mp (hbot ▸ mem_map_of_mem f hy)
    change MulAut.congr e (L.normalizerMonoidHom ⟨y,hYL hy⟩)=1 at hyf
    rw [←(MulAut.congr e).map_one,(MulAut.congr e).injective.eq_iff] at hyf
    have hyk : (⟨y,hYL hy⟩:N) ∈ L.normalizerMonoidHom.ker := hyf
    rw [normalizerMonoidHom_ker] at hyk
    exact hyk

end Theory.PSL2.OrdinaryBorel
