module

public import Stellmacher.SectionFiveToSeven.Defs
public import Stellmacher.BaumannIntermediate
public import Stellmacher.BaumannNormalizer

/-!
# Characteristic obstruction for the selected factor in (6.1)

Under Hypothesis 2 and the contradictory containment `B(S) ≤ O₂(P₂)`,
let `T` be a Sylow 2-subgroup of `E` whose ambient image is exactly `B(S)`.
If `E ∨ S = P₁`, no nontrivial characteristic subgroup of `T` has normal
image in `E`. The injective-map companion also accepts a native factor with an arbitrary
injective homomorphism into H; the subgroup version is its projection.
The supplied Sylow subgroup and image equality are retained exactly,
so this obstruction can be used by the selected-factor application
of Stellmacher (2.4).

The 2-core of `P₂` lies in `S`. Baumann heredity identifies its Baumann
subgroup with `B(S)`, which `P₂` therefore normalizes. Transport a
characteristic subgroup of `T` through the canonical equivalence with
`B(S)`; its ambient image `X` is normalized by `P₂`. If its native image
were normal in `E`, then `E ∨ S = P₁` would make `P₁` normalize `X` too.
Thus `X ≤ S` is a normal 2-subgroup of the actual join `P₁ ∨ P₂`.
The trivial 2-core of that join forces `X = 1`, and injectivity reflects
this equality back to the original subgroup of `T`.

Source: Stellmacher (6.1), Journal of Algebra 190 (1997), p.30, the
characteristic-subgroup obstruction just before the application of (2.4),
in `refs/latex/stellmacher-n-group.tex`. No assertion that the join is the
whole ambient group or that `E` is ambient normal is used.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

public theorem sixOne_factor_characteristic_obstruction_of_injective
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (hB : baumannIn S ≤ twoCoreIn P2)
    {E : Type*} [Group E] (f : E →* H) (hf : Function.Injective f)
    (T : Sylow 2 E)
    (hT : (T : Subgroup E).map f = baumannIn S)
    (hgen : f.range ⊔ S = P1) :
    ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup E).subtype).Normal := by
  classical
  let B := baumannIn S
  have hBS : B ≤ S := inf_le_left
  have hSP2 : S ≤ P2 := h.fiveOne.P2_mem.1.2.1.1
  have hQ2S : twoCoreIn P2 ≤ S := by
    obtain ⟨_, T2, hT2⟩ := h.fiveOne.P2_mem.1.2.1
    rw [← hT2]
    exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := P2)).le_sylow_of_normal T2)
  have hBeq : baumannIn (twoCoreIn P2) = B := by
    simpa [B, baumannIn, omegaOneCenter, omegaOneCenterAmbient] using
      baumann_eq_of_intermediate S (twoCoreIn P2) hB hQ2S
  have hQ2P2 : twoCoreIn P2 ≤ P2 := Subgroup.map_subtype_le _
  have hQ2normal : ((twoCoreIn P2).subgroupOf P2).Normal := by
    rw [twoCoreIn, subgroupOf_map_subtype_eq]
    infer_instance
  have hP2B : P2 ≤ Subgroup.normalizer (B : Set H) := by
    have hnorm := ((Subgroup.normal_subgroupOf_iff_le_normalizer hQ2P2).mp hQ2normal).trans
      (normalizer_le_normalizer_baumann (twoCoreIn P2))
    change P2 ≤ Subgroup.normalizer (baumannIn (twoCoreIn P2) : Set H) at hnorm
    rwa [hBeq] at hnorm
  let e : T ≃* B :=
    ((T : Subgroup E).equivMapOfInjective f hf).trans
      (MulEquiv.subgroupCongr hT)
  have he (x : T) : ((e x : B) : H) = f (x : E) := by
    simp only [e, MulEquiv.trans_apply]
    rw [MulEquiv.subgroupCongr_apply]
    exact Subgroup.coe_equivMapOfInjective_apply _ _ _ x
  intro K hKchar hKne hKnormal
  let KB : Subgroup B := K.map e.toMonoidHom
  have hKBchar : KB.Characteristic := by
    rw [Subgroup.characteristic_iff_map_le]
    intro φ x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨k, hk, rfl⟩ := hy
    let ψ : T ≃* T := e.trans (φ.trans e.symm)
    have hψK := (Subgroup.characteristic_iff_map_le.mp hKchar) ψ
    exact ⟨ψ k, hψK ⟨k, hk, rfl⟩, e.apply_symm_apply _⟩
  let X : Subgroup H := KB.map B.subtype
  have hXE : X = (K.map (T : Subgroup E).subtype).map f := by
    dsimp only [X, KB]
    rw [Subgroup.map_map, Subgroup.map_map]
    apply congrArg (fun f => K.map f)
    ext x
    exact he x
  have hXB : X ≤ B := Subgroup.map_subtype_le _
  have hXS : X ≤ S := hXB.trans hBS
  have hXE_le : X ≤ f.range := hXE ▸ Subgroup.map_le_range f _
  have hP2X : P2 ≤ Subgroup.normalizer (X : Set H) := by
    let _ : KB.Characteristic := hKBchar
    exact hP2B.trans
      (BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic B KB)
  have hEX : f.range ≤ Subgroup.normalizer (X : Set H) := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro _ ⟨e, rfl⟩ x hx
    rw [hXE] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨e * y * e⁻¹, hKnormal.conj_mem y hy e, by simp⟩
  have hP1X : P1 ≤ Subgroup.normalizer (X : Set H) := by
    rw [← hgen]
    exact sup_le hEX (hSP2.trans hP2X)
  let J := P1 ⊔ P2
  have hXJ : X ≤ J := hXS.trans (hSP2.trans le_sup_right)
  have hXnormal : (X.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXJ).mpr (sup_le hP1X hP2X)
  have hXp : IsPGroup 2 X := S0.isPGroup'.to_le (hXS.trans h.fiveOne.S_le_S0)
  have hXJp : IsPGroup 2 (X.subgroupOf J) :=
    hXp.comap_of_injective J.subtype J.subtype_injective
  have hXcore : X ≤ twoCoreIn J := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hXJ]
    exact Subgroup.map_mono (show X.subgroupOf J ≤ pCore 2 J from le_sSup ⟨hXnormal, hXJp⟩)
  have hXbot : X = ⊥ := le_bot_iff.mp (hXcore.trans_eq h.fiveOne.join_twoCore_eq_bot)
  apply hKne
  apply (Subgroup.map_eq_bot_iff_of_injective K (f := e.toMonoidHom) e.injective).mp
  exact (Subgroup.map_eq_bot_iff_of_injective KB B.subtype_injective).mp hXbot

/-- The subtype version retains the supplied Sylow witness of the ambient factor. -/
public theorem sixOne_factor_characteristic_obstruction
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (hB : baumannIn S ≤ twoCoreIn P2)
    (E : Subgroup H) (T : Sylow 2 E)
    (hT : (T : Subgroup E).map E.subtype = baumannIn S)
    (hgen : E ⊔ S = P1) :
    ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup E).subtype).Normal := by
  apply sixOne_factor_characteristic_obstruction_of_injective
    S0 S P1 P2 h hB E.subtype E.subtype_injective T hT
  simpa only [Subgroup.range_subtype] using hgen

end Stellmacher.SectionsFiveToSeven
