module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalRow.FixedVector
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalRow.PairAction
public import Theory.Representation.BinaryConjugationSection.DiagonalFixed
public import Theory.SpecificGroups.SL2.OddFixedVectors
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.BlockAlternative
public import CFSG.Quasithin.Chapter3.Section01.HStarOmegaCentralizer

/-!
# Faithful odd Hall action on the original Sylow omega-center

A noncentral vector fixed by the half-Sylow produces an index-two diagonal
in Ω₁Z(T). An odd-order orbit element centralizing that diagonal would fix
a nonzero natural vector in each active quotient factor. The odd natural
fixed-vector theorem and the orbit two-core kernel force it to be trivial.

Thus the original odd Hall acts faithfully on Ω₁Z(T), and H-star minimality
gives its centralizer in H as the prescribed Sylow T. The two fixed-center
identities and the common block alternative now apply to the same selected
component without an independent seed-centralizer premise. The actual
natural marking and original Hall containment remain the earlier inputs
owned by the moving-Hall assembly; this is not the terminal overcomponent
construction or the unconditional Hall three-group theorem.
Source: Aschbacher–Smith 10.1.2(5) and 10.2.3(4), printed pp.742,745–746.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

set_option backward.isDefEq.respectTransparency false in
private theorem source_natural_first_odd_not_centralizes_omegaCenter
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (q : localOrbit T L →* (SL(2,F) × SL(2,F)))
    (hfirst : ∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1))
    (hsecond : ∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l)))
    (b : localOrbit T L) (m : ℕ) (hm : Odd m)
    (hb : (q b).1 ^ m = 1) (hne : (q b).1 ≠ 1) :
    (b:G) ∉ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  have h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
    Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      D.simpleQTKE T D.maximal
  let R := localOrbit T L
  let W := ⁅D.fullModule,L⁆
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let nR := source_original_natural_first_orbit_section D hn ht htn hcross e n q hfirst hsecond
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hWT : W ≤ (T : Subgroup G) :=
    hWV.trans (D.fullModule_le_sylow h127)
  have hWS : W ≤ S := le_inf hWT
    (n.section_le.trans L.le_normalizer)
  obtain ⟨w,hwS,hwn⟩ := source_natural_moved_noncentral_fixed_vector D degree hdegree hF e n S
    (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right
    (T.isPGroup'.to_le inf_le_left)
  have hwomega : (w:G) ∈ omegaOneCenterAmbient S :=
    (mem_omegaOneCenterAmbient_iff S w).mpr
      ⟨hWS w.property,elemPow_eq_one_of_isElementaryAbelian (p:=2) (w:G) w.property,hwS⟩
  have hVt : t*(w:G)*t⁻¹ ∈ D.fullModule :=
    (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule
      (le_normalizer_componentOrbit L T ht)) w).mp (hWV w.property)
  let : IsElementaryAbelian 2 D.fullModule :=
    D.fullModule_elementary h127
  have hc : Commute (w:G) (t*w*t⁻¹) := congrArg D.fullModule.subtype
    (mul_comm (⟨w,hWV w.property⟩ : D.fullModule) ⟨t*w*t⁻¹,hVt⟩)
  have hRt : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T ht)
  have hRWt : R ≤ normalizer (W.map (MulAut.conj t).toMonoidHom : Set G) := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) nR.normalized
    rwa [hRt,map_normalizer_eq_of_bijective W (MulAut.conj t).bijective] at hh
  have hinter : W ⊓ W.map (MulAut.conj t).toMonoidHom ≤ sourceMovedFixed D :=
    le_inf inf_le_left (inf_le_right.trans hcross)
  have hiS : S.relIndex (T : Subgroup G) = 2 := by
    change ((T : Subgroup G) ⊓ normalizer (L : Set G)).relIndex (T : Subgroup G) = 2
    rw [inf_relIndex_left]
    exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  intro hbZ
  have he := nR.coordinates_conj_eq_of_centralizes_diagonal
    (S := S) (T := (T : Subgroup G)) inf_le_left hiS t ht (fun hs => htn hs.2)
    hinter w hwomega hc b (nR.normalized b.property) (hRWt b.property) hbZ
  have hf := nR.equivariant b w
  have hz := Matrix.SL2.odd_power_fixed_eq_zero (q b).1 m hm hb hne
    (nR.coordinates w).toAdd (hf.symm.trans (congrArg Multiplicative.toAdd he))
  exact hwn (Multiplicative.toAdd.injective hz)


/-- Odd-order elements of the literal original orbit cannot fix the Sylow omega-center. -/
theorem source_natural_odd_not_centralizes_omegaCenter
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (mark : NaturalMarking D e)
    (b : localOrbit T L) (m : ℕ) (hm : Odd m) (hb : b ^ m = 1) (hne : b ≠ 1) :
    (b:G) ∉ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  obtain ⟨⟨c⟩,t,ht,htn,hcross⟩ := mark
  obtain ⟨eR,hfirst,hsecond⟩ := source_original_natural_pair_quotient D degree hdegree hF e hn ht htn
  let q := eR.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))
  have hqne : q b ≠ 1 := by
    intro hz
    have hc : b ∈ pCore 2 (localOrbit T L) :=
      (QuotientGroup.eq_one_iff b).mp (eR.injective (hz.trans eR.map_one.symm))
    let bC : pCore 2 (localOrbit T L) := ⟨b,hc⟩
    have hcm : bC ^ m = 1 := Subtype.ext hb
    have ho := (pCore_isPGroup (p := 2) (G := localOrbit T L)).orderOf_coprime
      hm.coprime_two_left bC
    have hc1 : orderOf bC = 1 := by
      apply Nat.dvd_one.mp
      rw [←ho.gcd_eq_one]
      exact Nat.dvd_gcd dvd_rfl (orderOf_dvd_of_pow_eq_one hcm)
    exact hne (congrArg Subtype.val (orderOf_eq_one_iff.mp hc1))
  have hpow : (q b) ^ m = 1 := by rw [←map_pow,hb,map_one]
  by_cases hfirstne : (q b).1 ≠ 1
  · exact source_natural_first_odd_not_centralizes_omegaCenter D degree hdegree hF e hn
      ht htn hcross c q hfirst hsecond b m hm (congrArg Prod.fst hpow) hfirstne
  · have hsecondne : (q b).2 ≠ 1 := fun he => hqne (Prod.ext (not_ne_iff.mp hfirstne) he)
    let b' := originalOrbitConjugation ht b
    let β := e.symm.trans ((QuotientGroup.congr _ _ (originalSquareConjugation D hn ht)
      (pCore_map_iso 2 (originalSquareConjugation D hn ht))).trans e)
    have hex : q b' = (β (q b).2,(q b).1) :=
      source_natural_pair_conjugate D e hn ht htn q hfirst hsecond b
    have hp' : (q b').1 ^ m = 1 := by
      rw [hex,←map_pow]
      exact (congrArg β (congrArg Prod.snd hpow)).trans β.map_one
    have hn' : (q b').1 ≠ 1 := by
      rw [hex]
      exact fun he => hsecondne (β.injective (he.trans β.map_one.symm))
    intro hbZ
    apply source_natural_first_odd_not_centralizes_omegaCenter D degree hdegree hF e hn
      ht htn hcross c q hfirst hsecond b' m hm hp' hn'
    intro z hz
    have hzt := ((mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz).2.2 t ht
    have hzb := hbZ z hz
    change z*(t*(b:G)*t⁻¹) = (t*(b:G)*t⁻¹)*z
    have htiz : t⁻¹*z = z*t⁻¹ := (show Commute t z from hzt).inv_left.eq
    calc
      z*(t*(b:G)*t⁻¹) = (z*t)*(b:G)*t⁻¹ := by group
      _ = (t*z)*(b:G)*t⁻¹ := by rw [hzt]
      _ = t*(z*(b:G))*t⁻¹ := by group
      _ = t*((b:G)*z)*t⁻¹ := by rw [hzb]
      _ = (t*(b:G))*(z*t⁻¹) := by group
      _ = (t*(b:G))*(t⁻¹*z) := by rw [htiz]
      _ = (t*(b:G)*t⁻¹)*z := by group

/-- The original odd Hall acts faithfully on the seed once it lies in the orbit. -/
theorem Context.hall_seed_centralizer_eq_bot
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L) :
    B.map H.subtype ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro b hb
  by_contra hne
  have hbne : b ≠ 1 := hne
  let bB : B.map H.subtype := ⟨b,hb.1⟩
  have hpow : b ^ Nat.card (B.map H.subtype) = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := bB))
  exact source_natural_odd_not_centralizes_omegaCenter D degree hdegree hF e ctx.nonnormal
    mark ⟨b,hBR hb.1⟩ (Nat.card (B.map H.subtype))
    (ctx.odd_card_of_le_hall_image _ le_rfl) (Subtype.ext hpow)
    (fun he => hbne (congrArg Subtype.val he)) hb.2

/-- The seed centralizer is the prescribed Sylow, with no seed-action callback. -/
theorem Context.seed_centralizer_eq_sylow
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L) :
    centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype ctx.hstar.1.1.2 : Subgroup H) :=
  Chapter3.HStar.omega_center_centralizer_eq_sylow_of_hall ctx.hstar ctx.moving B
    ctx.hall_le ctx.hall (ctx.hall_seed_centralizer_eq_bot D degree hdegree hF e mark hBR)

/-- Both original fixed centers vanish under the natural marking and Hall placement. -/
theorem Context.fixed_centers_of_natural_marking
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥ ∧
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥ :=
  ctx.original_fixed_centers_eq_bot D degree hdegree hF e hBR
    (ctx.seed_centralizer_eq_sylow D degree hdegree hF e mark hBR)


open ChapterB ChapterC.GlaubermanNiles

/-- The same selected component and original block alternative, with the seed centralizer discharged. -/
theorem Context.selected_component_and_block_of_natural_marking
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L) :
    let S := T.subtype ctx.hstar.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let B₀ := baumann (S : Subgroup H)
    ∃ K : Subgroup H, K.IsCComponent ∧
      U ≤ normalizer (K : Set H) ∧ B₀ ≤ normalizer (K : Set H) ∧
      InLocalClass (inclusion (show B₀ ≤ K ⊔ B₀ from le_sup_right)) ∧
      (localV (inclusion (show B₀ ≤ K ⊔ B₀ from le_sup_right))).map
        (K ⊔ B₀).subtype = (⁅U,K⁆ : Subgroup H) ⊔
          (thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H)) ∧
      K ⊔ (S : Subgroup H) = ⊤ ∧
      (K = pResidual 2 H ∨
        ((thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H) ≠ ⊥) ∧
          (∃ E : ChapterB.QuasisimpleSource.BinaryField,
            Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,E.Carrier))) ∧
          ∃ t ∈ (S : Subgroup H),
            pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom)) ∧
      (ChapterC.IsBlock (L.subgroupOf (localJoin T L)) ∨
        (ChapterC.IsBlock K ∧ ∃ m, ChapterC.IsL2EvenBlock K m)) :=
  ctx.selected_component_and_block D n hn hF e hBR
    (ctx.seed_centralizer_eq_sylow D n hn hF e mark hBR)

end CFSG.Quasithin.Chapter10.MovingHall
