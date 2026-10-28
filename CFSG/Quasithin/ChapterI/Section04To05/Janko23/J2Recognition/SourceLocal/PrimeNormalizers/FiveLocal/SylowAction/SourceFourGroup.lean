module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.SourceFourGroup.Model
public import Theory.ElementaryAbelian.Quotient

/-!
# Constructing the marked source four-group in the literal automizer

The marked root normalizer embeds `D₁₀ × A₅` in G. The pentagon embedding
in its A₅ factor supplies an actual `D₁₀ × D₁₀`, whose rotation plane is
Sylow by the order of G. The dihedral marking identifies the first rotation
line with the root-family subgroup; the component marking puts the second
line in the centralizer of the marked conjugate of z.

Conjugating the entire embedding places this plane in any requested Sylow P.
Its reflection four-group acts through P's literal `normalizerMonoidHom`.
Self-centralization makes this action faithful, and the model fixed-line
calculation and the source separation give the marked configuration.

Source: Aschbacher, *Sporadic Groups* (1994), final paragraph of 47.2,
printed p.261 (PDF p.136). The root and two-central families remain explicit
inputs from the preceding branches. `exists_sourceFrame` supplies the marked
four-group premise of the subsequent Sylow action and fusion calculation.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.SourceFourGroup
variable {G : Type*} [Group G] [Finite G]
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The marked source configuration, with the order-five guard scoped over the
entire fixed-line equivalence. -/
structure Configuration (D : Seed G) (t : G) (P : Sylow 5 G) where
  four : Subgroup (automizer P)
  four_elementary : IsElementaryAbelian 2 four
  four_card : Nat.card four = 4
  A : Subgroup P
  B : Subgroup P
  A_card : Nat.card A = 5
  B_card : Nat.card B = 5
  fixed : ∀ (L : Subgroup P) (_ : Nat.card L = 5),
    (∀ v : four, L.map v.val.val.toMonoidHom = L) ↔ L = A ∨ L = B
  nonfusion : ¬ InLineOrbit (automizer P) A B
  root : FiveCentralizing t (lineImage P A)
  twoCentral : FiveCentralizing D.z (lineImage P B)

/-- An embedded product model whose rotation plane is P gives its literal action frame. -/
theorem configuration_of_embedding {D : Seed G} {t : G} (hB : TwoCentralFiveFamily D t)
    (P : Sylow 5 G) (f : Model.M →* G) (hf : Function.Injective f)
    (hP : Model.plane.map f = (P : Subgroup G))
    (hAmark : FiveCentralizing t (Model.A.map f))
    (hBmark : FiveCentralizing D.z (Model.B.map f)) : Nonempty (Configuration D t P) := by
  let n : Model.four →* normalizer (P : Set G) :=
    (f.comp Model.four.subtype).codRestrict _ (by
      intro v
      change f v ∈ normalizer ((P : Subgroup G) : Set G)
      rw [← hP]
      exact Model.plane.le_normalizer_map f ⟨v, Model.normalizes_plane v.property, rfl⟩)
  let a : Model.four →* automizer P := (P : Subgroup G).normalizerMonoidHom.rangeRestrict.comp n
  have ha : Function.Injective a := by
    apply a.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro v hv
    have hker : n v ∈ (P : Subgroup G).normalizerMonoidHom.ker := congrArg Subtype.val hv
    rw [normalizerMonoidHom_ker] at hker
    change f v ∈ centralizer (P : Set G) at hker
    rw [hB.self_centralizing P, ← hP] at hker
    obtain ⟨w, hw, he⟩ := hker
    have hvp : (v : Model.M) ∈ Model.plane := hf he ▸ hw
    exact Subtype.ext (Model.four_inf_plane v v.property hvp)
  let A := (Model.A.map f).subgroupOf (P : Subgroup G)
  let B := (Model.B.map f).subgroupOf (P : Subgroup G)
  have hAP : Model.A.map f ≤ (P : Subgroup G) := hP ▸ map_mono Model.A_le_plane
  have hBP : Model.B.map f ≤ (P : Subgroup G) := hP ▸ map_mono Model.B_le_plane
  have hAi : lineImage P A = Model.A.map f := map_subgroupOf_eq_of_le hAP
  have hBi : lineImage P B = Model.B.map f := map_subgroupOf_eq_of_le hBP
  have hAc : Nat.card A = 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv, card_map_of_injective hf, Model.card_A]
  have hBc : Nat.card B = 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBP).toEquiv, card_map_of_injective hf, Model.card_B]
  have hfixed (L : Subgroup P) (hL : Nat.card L = 5) :
      (∀ v : a.range, L.map v.val.val.toMonoidHom = L) ↔ L = A ∨ L = B := by
    let L₀ := (lineImage P L).comap f
    have hLrange : lineImage P L ≤ f.range := by
      exact (map_subtype_le L).trans (hP ▸ map_le_range f Model.plane)
    have hLmap : L₀.map f = lineImage P L := map_comap_eq_self hLrange
    have hL₀ : Nat.card L₀ = 5 := by
      rw [← card_map_of_injective hf, hLmap, lineImage,
        card_map_of_injective (P : Subgroup G).subtype_injective, hL]
    have hL₀P : L₀ ≤ Model.plane := by
      have h := comap_mono (map_subtype_le L : lineImage P L ≤ (P : Subgroup G)) (f := f)
      exact h.trans_eq ((congrArg (comap f) hP.symm).trans
        (comap_map_eq_self_of_injective hf Model.plane))
    have hn : (∀ v : a.range, L.map v.val.val.toMonoidHom = L) ↔
        (∀ v ∈ Model.four, v ∈ normalizer (L₀ : Set Model.M)) := by
      constructor
      · intro h v hv
        have he := h ⟨a ⟨v, hv⟩, ⟨⟨v, hv⟩, rfl⟩⟩
        have himg := congrArg (lineImage P) he
        change lineImage P (L.map ((P : Subgroup G).normalizerMonoidHom (n ⟨v, hv⟩)).toMonoidHom) = _ at himg
        rw [lineImage_action] at himg
        have hm : f v ∈ normalizer (lineImage P L : Set G) :=
          mem_normalizer_iff_map_conj_eq.mpr himg
        exact (lineImage P L).le_normalizer_comap f hm
      · intro h v
        obtain ⟨w, hw⟩ := v.property
        apply map_injective (P : Subgroup G).subtype_injective
        change lineImage P (L.map v.val.val.toMonoidHom) = lineImage P L
        have hv : v.val.val = (P : Subgroup G).normalizerMonoidHom (n w) :=
          congrArg Subtype.val hw.symm
        rw [hv, lineImage_action]
        apply mem_normalizer_iff_map_conj_eq.mp
        rw [← hLmap]
        exact L₀.le_normalizer_map f ⟨w, h w w.property, rfl⟩
    rw [hn, Model.fixed_lines L₀ hL₀ hL₀P]
    have hEq (K : Subgroup Model.M) (J : Subgroup P)
        (hJ : lineImage P J = K.map f) : L₀ = K ↔ L = J := by
      rw [← (map_injective hf).eq_iff, hLmap, ← hJ]
      exact (map_injective (P : Subgroup G).subtype_injective).eq_iff
    rw [hEq Model.A A hAi, hEq Model.B B hBi]
  refine ⟨{
    four := a.range
    four_elementary := IsElementaryAbelian.of_surjective a.rangeRestrict a.rangeRestrict_surjective
    four_card := (Nat.card_congr (MonoidHom.ofInjective ha).toEquiv).symm.trans Model.card_four
    A := A
    B := B
    A_card := hAc
    B_card := hBc
    fixed := hfixed
    nonfusion := nonfusion_of_markings hB P A B (hAi ▸ hAmark) (hBi ▸ hBmark)
    root := hAi ▸ hAmark
    twoCentral := hBi ▸ hBmark
  }⟩

/-- The marked source product supplies the embedded double-pentagon model. -/
theorem embedding_of_root {D : Seed G} {t : G} {E : Subgroup G}
    (hE : FiveCentralizing t E) (W : RootFiveWitness D E) :
    ∃ f : Model.M →* G, Function.Injective f ∧
      FiveCentralizing t (Model.A.map f) ∧ FiveCentralizing D.z (Model.B.map f) := by
  let N := normalizer (E : Set G)
  let e : (DihedralGroup 5 × alternatingGroup (Fin 5)) →* G :=
    N.subtype.comp W.equiv.symm.toMonoidHom
  have he : Function.Injective e := N.subtype_injective.comp W.equiv.symm.injective
  let j := (MonoidHom.id (DihedralGroup 5)).prodMap alternatingGroup.FiveLocalGeometry.dihedralHom
  have hj : Function.Injective j := by
    intro x y h
    apply Prod.ext
    · exact congrArg (fun z : DihedralGroup 5 × alternatingGroup (Fin 5) => z.1) h
    · exact alternatingGroup.FiveLocalGeometry.dihedralHom_injective (congrArg Prod.snd h)
  let f := e.comp j
  have hf : Function.Injective f := he.comp hj
  have hEA : E ≤ Model.A.map f := by
    intro x hx
    have hxd : x ∈ ((⊤ : Subgroup (DihedralGroup 5)).prod
        (⊥ : Subgroup (alternatingGroup (Fin 5)))).map e := by
      rw [show ((⊤ : Subgroup (DihedralGroup 5)).prod
        (⊥ : Subgroup (alternatingGroup (Fin 5)))).map e = E ⊔ zpowers W.inverter
        from W.dihedral_factor]
      exact (le_sup_left : E ≤ E ⊔ zpowers W.inverter) hx
    obtain ⟨⟨d, c⟩, hd, hdx⟩ := hxd
    have hc : c = 1 := mem_bot.mp hd.2
    subst c
    have hx5 : x ^ 5 = 1 := by
      have h := pow_card_eq_one' (x := (⟨x, hx⟩ : E))
      rw [hE.1] at h
      exact congrArg Subtype.val h
    have hd5 : d ^ 5 = 1 := by
      have hp : (d, (1 : alternatingGroup (Fin 5))) ^ 5 = 1 := by
        apply he
        rw [map_pow, hdx, hx5, map_one]
      exact congrArg Prod.fst hp
    refine ⟨(d, 1), ⟨Model.rotations_of_fifth_power d hd5, mem_bot.mpr rfl⟩, ?_⟩
    simpa only [f, j, MonoidHom.comp_apply, MonoidHom.coe_prodMap,
      Prod.map_apply, MonoidHom.id_apply, map_one] using hdx
  have hAE : Model.A.map f = E := by
    apply (eq_of_le_of_card_ge hEA _).symm
    rw [card_map_of_injective hf, Model.card_A, hE.1]
  have hBC : Model.B.map f ≤ fiveComponent E := by
    rintro _ ⟨⟨d, c⟩, hc, rfl⟩
    rw [← W.component_factor]
    refine ⟨j (d, c), ⟨?_, mem_top _⟩, rfl⟩
    exact hc.1
  refine ⟨f, hf, hAE ▸ hE, ?_⟩
  exact ⟨by rw [card_map_of_injective hf, Model.card_B],
    W.inverter, W.inverter_conj, hBC.trans W.component_le⟩

/-- Conjugate the whole marked configuration to an arbitrary Sylow subgroup. -/
theorem exists_configuration {D : Seed G} (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D)
    (hA : RootFiveFamily D S.t) (hB : TwoCentralFiveFamily D S.t)
    (P : Sylow 5 G) : Nonempty (Configuration D S.t P) := by
  have ht : 5 ^ (Nat.card (involutionCentralizer S.t)).factorization 5 = 5 := by
    rw [S.model.centralizer_card]
    decide +kernel
  obtain ⟨E, hE, hEt⟩ := exists_fiveCentralizing S.t ht
  have hEf : FiveCentralizing S.t E := ⟨hE, S.t, IsConj.refl _, hEt⟩
  obtain ⟨W⟩ := hA E hEf
  obtain ⟨f, hf, hAf, hBf⟩ := embedding_of_root hEf W
  have hcard : Nat.card (Model.plane.map f) = 5 ^ (Nat.card G).factorization 5 := by
    rw [card_map_of_injective hf, Model.card_plane, hG]
    decide +kernel
  let P₀ : Sylow 5 G := Sylow.ofCard (Model.plane.map f) hcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hp : Model.plane.map f' = (P : Subgroup G) := by
    rw [← map_map]
    exact congrArg (fun Q : Sylow 5 G => (Q : Subgroup G)) hg
  apply configuration_of_embedding hB P f' ((MulAut.conj g).injective.comp hf) hp
  · rw [← map_map]
    exact fiveCentralizing_conjugate hAf g
  · rw [← map_map]
    exact fiveCentralizing_conjugate hBf g

/-- The two preceding source families construct the marked four-group frame
in every Sylow-five automizer. This discharges the `hframes` premise of
`family_of_frames_and_linear_calculation`; the root and two-central families
remain explicit inputs for its source-theorem assembly owner. -/
theorem exists_sourceFrame {D : Seed G} (hG : Nat.card G = 604800)
    (S : InvolutionGeometry.SelectedGeometry D)
    (hA : RootFiveFamily D S.t) (hB : TwoCentralFiveFamily D S.t)
    (P : Sylow 5 G) : Nonempty (SourceFrame D S.t P) := by
  obtain ⟨C⟩ := exists_configuration hG S hA hB P
  exact ⟨{
    frame := {
      four := C.four
      four_elementary := C.four_elementary
      four_card := C.four_card
      A := C.A
      B := C.B
      A_card := C.A_card
      B_card := C.B_card
      fixed := C.fixed
      nonfusion := C.nonfusion
    }
    root := C.root
    twoCentral := C.twoCentral
  }⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.SourceFourGroup
