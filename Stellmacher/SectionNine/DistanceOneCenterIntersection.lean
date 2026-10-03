module

public import Stellmacher.SectionNine.DistanceOneExtraction
public import Stellmacher.SectionNine.DistanceOneReduction

/-!
# The intersection in the distance-one extraction

The cardinal bound in (4), together with the center order in (8), already
identifies the intersection. If the second product factor were the whole
second center, the extracted join would stabilize the first vertex. Its
conjugator would then normalize the first center, collapsing the two centers
and contradicting (4). The second factor consequently has order at most
eight, and its index over the intersection is at least four. The nontrivial
next center is contained in both factors by the Sylow-center description
and conjugation invariance. This is the intersection identity immediately
before the maximal subgroup construction in Stellmacher (9.1), journal p.47.
The extraction witness and the genuine index inequality are explicit inputs;
no assertion about an ambient quadratic action is used.
-/

namespace Stellmacher.SectionNine

open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext
open Stellmacher.SectionsFiveToSeven.SevenSix

universe u

private theorem normalized_join_index {G : Type u} [Group G]
    (C D : Subgroup G) (hn : D ≤ Subgroup.normalizer (C : Set G)) :
    C.relIndex (C ⊔ D) = (C ⊓ D).relIndex D := by
  let V := C ⊔ D
  let _ : (C.subgroupOf V).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hn)
  have h := Subgroup.relIndex_sup_left (D.subgroupOf V) (C.subgroupOf V)
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
    Subgroup.relIndex_subgroupOf le_rfl,
    Subgroup.relIndex_subgroupOf le_sup_right] at h
  exact h.trans (Subgroup.inf_relIndex_right C D).symm

private theorem card_mul_relIndex {G : Type u} [Group G]
    (C D : Subgroup G) (hle : C ≤ D) :
    Nat.card C * C.relIndex D = Nat.card D := by
  have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) C D bot_le hle
  simpa only [Subgroup.relIndex_bot_left] using h

public theorem distance_one_center_intersection_eq_of_extraction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (data : DistanceOneExtractionData ctx)
    (hfour :
      let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
      let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
        (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
      4 ≤ (V ⊓ q ctx.Γ ctx.criticalPath.a).relIndex V) :
    z ctx.Γ ctx.criticalPath.a ⊓
        z ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a) =
      z ctx.Γ ctx.criticalPath.a' := by
  let Gamma := ctx.Γ
  let cp := ctx.criticalPath
  have hlen : cp.length = 1 := hb
  let next := Gamma.act data.x⁻¹ cp.a
  let Za := z Gamma cp.a
  let Zc := z Gamma next
  let C := Za ⊓ stabilizer Gamma next
  let D := Zc ⊓ stabilizer Gamma cp.a
  let V := C ⊔ D
  have hgeometry := distance_one_product_factors Gamma cp.a next
  have hcore := distance_one_extracted_core_intersection ctx hb data
  have hindex : 4 ≤ C.relIndex V := by
    change 4 ≤ (V ⊓ q Gamma cp.a).relIndex V at hfour
    rw [hcore] at hfour
    exact hfour
  have hCD : C ⊓ D = Za ⊓ Zc := hgeometry.2.2.2.2
  have hindexD : 4 ≤ (Za ⊓ Zc).relIndex D := by
    rw [← hCD, ← normalized_join_index C D hgeometry.2.1]
    exact hindex
  have hZa : Nat.card Za = 16 := hfaith.1
  have hZc : Nat.card Zc = 16 := by
    change Nat.card (z Gamma (Gamma.act data.x⁻¹ cp.a)) = 16
    rw [z_act, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact hZa
  have hZaGa : Za ≤ stabilizer Gamma cp.a := by
    have hn : cp.a' ∈ neighborhood Gamma cp.a := by
      rw [neighborhood, Gamma.neighbors_def]
      exact (Gamma.distance_symm _ _).trans (cp.endpoint_distance.trans hb)
    have hq : q Gamma cp.a ≤ stabilizer Gamma cp.a := by
      rw [q, Gamma.twoCoreAt_def]
      exact twoCoreIn_le _
    exact ((lemma_seven_three ctx.sectionSeven Gamma).center_core cp.a cp.a' hn).trans
      ((omegaOneCenter_le_centerAmbient _).trans
        ((Subgroup.map_subtype_le _).trans hq))
  have hproper : ¬ Zc ≤ D := by
    intro hle
    have hZcGa : Zc ≤ stabilizer Gamma cp.a := hle.trans inf_le_right
    have hEGa : data.E ≤ stabilizer Gamma cp.a :=
      data.generated ▸ sup_le hZaGa hZcGa
    have hxnorm := stabilizer_le_normalizer_z Gamma cp.a (hEGa data.x_mem_E)
    have heq : Zc = Za := by
      change z Gamma (Gamma.act data.x⁻¹ cp.a) = Za
      rw [z_act, inv_inv]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hxnorm
    have hDV : D ≤ C := by
      change Zc ⊓ stabilizer Gamma cp.a ≤ C
      rw [heq]
      have hCeq : C = Za := by
        apply inf_eq_left.mpr
        have hZcle : Zc ≤ stabilizer Gamma next := by
          change z Gamma (Gamma.act data.x⁻¹ cp.a) ≤
            stabilizer Gamma (Gamma.act data.x⁻¹ cp.a)
          rw [stabilizer_act, z_act, inv_inv]
          exact Subgroup.map_mono hZaGa
        exact heq ▸ hZcle
      rw [hCeq]
      exact inf_le_left
    have hVe : V = C := sup_eq_left.mpr hDV
    rw [hVe, Subgroup.relIndex_self] at hindex
    omega
  have hDindex : 2 ≤ D.relIndex Zc := by
    have hne : D.relIndex Zc ≠ 1 := fun heq =>
      hproper (Subgroup.relIndex_eq_one.mp heq)
    have hpos : 0 < D.relIndex Zc :=
      Nat.pos_of_ne_zero (D.subgroupOf Zc).index_ne_zero_of_finite
    omega
  have hDcard : Nat.card D ≤ 8 := by
    have hmul := card_mul_relIndex D Zc inf_le_left
    rw [hZc] at hmul
    nlinarith
  have hintercard : Nat.card (Za ⊓ Zc : Subgroup G) ≤ 2 := by
    have hmul := card_mul_relIndex (Za ⊓ Zc) D
      (hCD ▸ (inf_le_right : C ⊓ D ≤ D))
    nlinarith
  have hfirst : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1, by omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        exact hb.symm
      _ = cp.a' := cp.path_end
  have homega : z Gamma cp.a' = omegaOneCenter T := by
    rw [← hfirst]
    exact (lemma_seven_five ctx.sectionSeven Gamma cp ctx.commutator_eq).next_center.1
  have hnextZa : z Gamma cp.a' ≤ Za := by
    rw [homega]
    obtain ⟨_, sylow, hsylow⟩ := (edge_sylow_data ctx.sectionSeven Gamma cp).1
    change omegaOneCenter T ≤ z Gamma cp.a
    rw [z, Gamma.zAt_def]
    exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩
  have hnextZc : z Gamma cp.a' ≤ Zc := by
    have hxnorm := stabilizer_le_normalizer_z Gamma cp.a' data.x_mem
    have hmap := Subgroup.map_mono (f := (MulAut.conj data.x).toMonoidHom) hnextZa
    have heq : (z Gamma cp.a').map (MulAut.conj data.x).toMonoidHom = z Gamma cp.a' :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxnorm
    rw [heq] at hmap
    simpa only [Zc, next, z_act, inv_inv] using hmap
  have hnontrivial : z Gamma cp.a' ≠ ⊥ := by
    rw [homega]
    have hTp : IsPGroup 2 T := by
      obtain ⟨_, sylow, hsylow⟩ := (edge_sylow_data ctx.sectionSeven Gamma cp).1
      rw [← hsylow]
      exact sylow.isPGroup'.map _
    let _ : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 ctx.sectionSeven.S_nontrivial
    let _ : Nontrivial (Subgroup.center T) := hTp.center_nontrivial
    obtain ⟨power, hpos, hcard⟩ :=
      (hTp.to_subgroup (Subgroup.center T)).nontrivial_iff_card.mp inferInstance
    have hdvd : 2 ∣ Nat.card (Subgroup.center T) := by
      rw [hcard]
      exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hpos)
    have hinner := omega₁_map_subtype_ne_bot (G := T) (Subgroup.center T) 2 hdvd
    intro hbot
    apply hinner
    apply Subgroup.map_injective (f := T.subtype) T.subtype_injective
    simpa [omegaOneCenter] using hbot
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hnextZa hnextZc)
    (hintercard.trans ((Subgroup.one_lt_card_iff_ne_bot _).mpr hnontrivial))).symm

end Stellmacher.SectionNine
