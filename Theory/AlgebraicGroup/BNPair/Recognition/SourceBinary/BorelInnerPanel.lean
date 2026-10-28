module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OddOuterPanel
public import Theory.GroupAction.ModelConjugation.InnerImage

/-!
# The panel kernel from inner Borel two-group actors

Suppose a normal endpoint factor supplements the full Borel. The unipotent
Sylow acts on its two-core quotient, preserves its quotient Sylow, and acts
trivially on the full Sylow-normalizer quotient. A concrete Borel-actor
calculation can therefore make every such actor inner by a Sylow element.
Their difference fixes the entire panel: use the factor's transitivity and
the literal quotient representative equation. No centerfreeness is needed,
so odd scalar covers are retained.

The resulting Sylow/radical supplement and the canonical root index force
U intersect U^s into the full panel kernel. BorelTwoInner records only the
model automorphism calculation, transports through actual equivalences,
and is proved for the unitary models in UnitaryPanelModel. The source
adapter supplies the original factor, normalizer and quotient-Sylow count.
Source: Fong--Seitz I (2B), pp.7--9; the canonical roots of (3A)--(3C),
pp.12--13. This criterion does not discard the type VI exception.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel

/-- Two-group actors preserving the root and fixing the Borel quotient are root inner. -/
@[expose] def BorelTwoInner {H : Type*} [Group H] (T B : Subgroup H) : Prop :=
  ∀ A : Subgroup (MulAut H), IsPGroup 2 A → T.map MulAut.conj ≤ A →
    ∀ a ∈ A, T.map a.toMonoidHom = T →
      (∀ x ∈ B, a x * x⁻¹ ∈ T) → a ∈ T.map MulAut.conj

 theorem BorelTwoInner.of_equiv {H K : Type*} [Group H] [Group K]
    {T B : Subgroup H} {U C : Subgroup K} (e : H ≃* K)
    (hT : T.map e.toMonoidHom = U) (hB : B.map e.toMonoidHom = C)
    (h : BorelTwoInner U C) : BorelTwoInner T B := by
  intro A hA hTA a ha hroot hdisp
  let f := (MulAut.congr e).toMonoidHom
  let A' := A.map f
  have hconj : (T.map MulAut.conj).map f = U.map MulAut.conj := by
    rw [← hT, map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    exact MulAut.congr_conj e x
  have hact (x : H) : MulAut.congr e a (e x) = e (a x) := by simp
  have hu : U.map (MulAut.congr e a).toMonoidHom = U := by
    rw [← hT, map_map]
    have he : (MulAut.congr e a).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp a.toMonoidHom := by ext x; exact hact x
    rw [he, ← map_map, hroot]
  have hd : ∀ y ∈ C, MulAut.congr e a y * y⁻¹ ∈ U := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := hB.symm ▸ hy
    change MulAut.congr e a (e x) * (e x)⁻¹ ∈ U
    rw [hact, ← map_inv, ← map_mul, ← hT]
    exact mem_map_of_mem _ (hdisp x hx)
  have ha' := h A' (hA.map f) (hconj ▸ map_mono hTA)
    (MulAut.congr e a) (mem_map_of_mem f ha) hu hd
  rw [← hconj] at ha'
  obtain ⟨b,hb,he⟩ := ha'
  exact (MulAut.congr e).injective he ▸ hb

/-- Transport a single Sylow calculation to every Sylow of the same finite group. -/
theorem BorelTwoInner.sylow {H : Type*} [Group H] [Finite H]
    (S T : Sylow 2 H)
    (h : BorelTwoInner (S : Subgroup H) (normalizer (S : Set H))) :
    BorelTwoInner (T : Subgroup H) (normalizer (T : Set H)) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H T S
  have hm : (T : Subgroup H).map (MulAut.conj g).toMonoidHom = S :=
    congrArg (fun R : Sylow 2 H => (R : Subgroup H)) hg
  apply BorelTwoInner.of_equiv (MulAut.conj g) hm _ h
  change (normalizer ((T : Subgroup H) : Set H)).map (MulAut.conj g).toMonoidHom = _
  rw [map_equiv_normalizer_eq,hm]
  rfl

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem action_kernel_le_panel (i : Fin 2) (A : Subgroup (X ⧸ Q.D))
    (hn : Q.tits.standardParabolic {Q.simple i} ≤ normalizer (A : Set (X ⧸ Q.D)))
    (hgen : A ⊔ Q.tits.B = Q.tits.standardParabolic {Q.simple i})
    (hcore : A.pCoreIn 2 ≤ Q.tits.B)
    (hUA : split.U ≤ normalizer (A : Set (X ⧸ Q.D))) (k : split.U)
    (hk : ∀ a : A, QuotientGroup.mk' (pCore 2 A)
        (A.normalizerMonoidHom ⟨k,hUA k.property⟩ a) =
          QuotientGroup.mk' (pCore 2 A) a) : (k : X ⧸ Q.D) ∈ localKernel Q i := by
  let M := Q.tits.standardParabolic {Q.simple i}
  have hUM : split.U ≤ M := split.U_le.trans (Q.tits.B_le_standardParabolic _)
  let kM : M := ⟨k,hUM k.property⟩
  refine ⟨kM, ?_, rfl⟩
  rw [normalCore_eq_ker]
  change MulAction.toPermHom M (Panel Q i) kM = 1
  ext c
  induction c using Quotient.inductionOn with | h g =>
    have hg : (g : X ⧸ Q.D) ∈ (A : Set (X ⧸ Q.D)) * (Q.tits.B : Set (X ⧸ Q.D)) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ ((Q.tits.B_le_standardParabolic _).trans hn), hgen]
      exact g.property
    obtain ⟨a,ha,b,hb,he⟩ := hg
    let aa : A := ⟨a,ha⟩
    let ac := A.normalizerMonoidHom
      ⟨k,hUA k.property⟩ aa
    have hq : QuotientGroup.mk' (pCore 2 A) ac = QuotientGroup.mk' (pCore 2 A) aa := hk aa
    have hc : aa⁻¹ * ac ∈ pCore 2 A := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 A) (aa⁻¹ * ac) = 1
      rw [map_mul,map_inv,hq,inv_mul_cancel]
    have hcb : a⁻¹ * (k * a * (k : X ⧸ Q.D)⁻¹) ∈ Q.tits.B :=
      hcore (mem_map_of_mem A.subtype hc)
    have hkb : a⁻¹ * k * a ∈ Q.tits.B := by
      have hh := Q.tits.B.mul_mem hcb (split.U_le k.property)
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
    have hgb : (g : X ⧸ Q.D)⁻¹ * k * g ∈ Q.tits.B := by
      rw [← he,_root_.mul_inv_rev]
      convert Q.tits.B.mul_mem (Q.tits.B.mul_mem (Q.tits.B.inv_mem hb) hkb) hb using 1
      group
    change QuotientGroup.mk (kM * g) = QuotientGroup.mk g
    apply QuotientGroup.eq.mpr
    change (((k : X ⧸ Q.D) * g)⁻¹ * g) ∈ Q.tits.B
    convert Q.tits.B.inv_mem hgb using 1
    group

private theorem borel_two_inner_action (i : Fin 2)
    (A : Subgroup (X ⧸ Q.D))
    (hn : Q.tits.standardParabolic {Q.simple i} ≤ normalizer (A : Set (X ⧸ Q.D)))
    (T : Sylow 2 A) (hTU : (T : Subgroup A).map A.subtype ≤ split.U)
    (hNB : ((normalizer (((T : Subgroup A).map (QuotientGroup.mk' (pCore 2 A))) :
        Set (A ⧸ pCore 2 A))).comap (QuotientGroup.mk' (pCore 2 A))).map A.subtype ≤ Q.tits.B)
    (hi : BorelTwoInner
      ((T : Subgroup A).map (QuotientGroup.mk' (pCore 2 A)))
      (normalizer (((T : Subgroup A).map (QuotientGroup.mk' (pCore 2 A))) : Set _)))
 :
    ∀ u : split.U,
      pCoreJoinAction 2 ((split.U_le.trans (Q.tits.B_le_standardParabolic _)).trans hn)
        (inclusion le_sup_right u) ∈
          ((T : Subgroup A).map (QuotientGroup.mk' (pCore 2 A))).map MulAut.conj := by
  let q := QuotientGroup.mk' (pCore 2 A)
  let Tbar := (T : Subgroup A).map q
  have hUM : split.U ≤ Q.tits.standardParabolic {Q.simple i} :=
    split.U_le.trans (Q.tits.B_le_standardParabolic _)
  have hUA : split.U ≤ normalizer (A : Set (X ⧸ Q.D)) := hUM.trans hn
  have hUT : split.U.subgroupOf A = (T : Subgroup A) :=
    T.is_maximal' split.isTwo.comap_subtype (map_le_iff_le_comap.mp hTU)
  let f : split.U →* MulAut (A ⧸ pCore 2 A) :=
    (pCoreJoinAction 2 hUA).comp (inclusion le_sup_right)
  have hRA : Tbar.map MulAut.conj ≤ f.range := by
    rintro _ ⟨_,⟨t,ht,rfl⟩,rfl⟩
    refine ⟨⟨t,hTU (mem_map_of_mem A.subtype ht)⟩,?_⟩
    exact pCoreJoinAction_on_component 2 hUA t
  have hdisp (u : split.U) : ∀ x ∈ normalizer (Tbar : Set _), f u x * x⁻¹ ∈ Tbar := by
    intro x hx
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) x
    have hab : (a : X ⧸ Q.D) ∈ Q.tits.B := hNB (mem_map_of_mem A.subtype hx)
    let au := A.normalizerMonoidHom ⟨u,hUA u.property⟩ a
    have hU : ((au * a⁻¹ : A) : X ⧸ Q.D) ∈ split.U := by
      change (u : X ⧸ Q.D) * a * (u : X ⧸ Q.D)⁻¹ * (a : X ⧸ Q.D)⁻¹ ∈ split.U
      have hnU := (mem_normalizer_iff.mp (split.normalizes hab) (u : X ⧸ Q.D)⁻¹).mp
        (split.U.inv_mem u.property)
      simpa only [mul_assoc] using split.U.mul_mem u.property hnU
    have hT : au * a⁻¹ ∈ (T : Subgroup A) := hUT ▸ hU
    change pCoreJoinAction 2 hUA (inclusion le_sup_right u) (q a) * (q a)⁻¹ ∈ Tbar
    rw [pCoreJoinAction_mk]
    exact mem_map_of_mem q hT
  intro u
  change f u ∈ Tbar.map MulAut.conj
  apply hi f.range (split.isTwo.of_surjective f.rangeRestrict f.rangeRestrict_surjective) hRA (f u) ⟨u,rfl⟩ ?_ (hdisp u)
  change Tbar.map (f u).toMonoidHom = Tbar
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    have hh := Tbar.mul_mem (hdisp u x (Tbar.le_normalizer hx)) hx
    change (f u) x ∈ Tbar
    simpa only [inv_mul_cancel_right] using hh
  · exact le_of_eq (card_map_of_injective (K := Tbar) (f := (f u).toMonoidHom) (f u).injective).symm

private theorem remainder_le_kernel_of_sylow_supplement (i : Fin 2)
    (A : Subgroup (X ⧸ Q.D)) (T : Sylow 2 A)
    (hTU : (T : Subgroup A).map A.subtype ≤ split.U)
    (hSR : (T : Subgroup A).map A.subtype ⊔ LocalCover.radical Q split i = split.U)
    (hAR : A.pCoreIn 2 ≤ LocalCover.radical Q split i)
    (hc : Nat.card (simpleRoot Q split i) =
      Nat.card ((T : Subgroup A).map (QuotientGroup.mk' (pCore 2 A)))) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  let R := LocalCover.radical Q split i
  let S := (T : Subgroup A).map A.subtype
  have hUM : split.U ≤ Q.tits.standardParabolic {Q.simple i} :=
    split.U_le.trans (Q.tits.B_le_standardParabolic _)
  have hind : R.relIndex split.U = R.relIndex S := by
    let R' := R.subgroupOf split.U
    let S' := S.subgroupOf split.U
    let : R'.Normal := normal_subgroupOf_of_le_normalizer
      (hUM.trans (LocalCover.radical_parabolic_normalizes Q split i))
    have hjoin : S' ⊔ R' = ⊤ := by
      rw [← subgroupOf_sup hTU (show R ≤ split.U from inf_le_left), hSR, subgroupOf_self]
    calc
      R.relIndex split.U = R'.relIndex (⊤ : Subgroup split.U) := by
        rw [relIndex_top_right]; rfl
      _ = R'.relIndex (S' ⊔ R') := congrArg (R'.relIndex ·) hjoin.symm
      _ = R'.relIndex S' := relIndex_sup_right _ _
      _ = R.relIndex S := relIndex_subgroupOf hTU
  have hbound : R.relIndex split.U ≤ Nat.card (simpleRoot Q split i) := by
    rw [hind,hc]
    have hle := relIndex_le_of_le_left (L := S) hAR
      (show (A.pCoreIn 2).relIndex S ≠ 0 from index_ne_zero_of_finite)
    have he : (A.pCoreIn 2).relIndex S =
        Nat.card ((T : Subgroup A).map (QuotientGroup.mk' (pCore 2 A))) := by
      rw [pCoreIn, relIndex_map_map_of_injective _ _ A.subtype_injective]
      simpa only [QuotientGroup.ker_mk'] using
        (relIndex_ker (T : Subgroup A) (QuotientGroup.mk' (pCore 2 A)))
    exact he ▸ hle
  have hRV : R ≤ simpleRemainder Q split i := unipotent_inf_kernel_le_remainder Q split i
  have hle : simpleRemainder Q split i ≤ R := by
    apply relIndex_eq_one.mp
    have he := relIndex_mul_relIndex R (simpleRemainder Q split i) split.U hRV inf_le_left
    have hv : (simpleRemainder Q split i).relIndex split.U =
        Nat.card (simpleRoot Q split i) := simpleRemainder_index Q split i
    rw [hv] at he
    have hpos := Nat.card_pos (α := simpleRoot Q split i)
    have hpos' : 0 < R.relIndex (simpleRemainder Q split i) :=
      Nat.pos_of_ne_zero index_ne_zero_of_finite
    nlinarith
  exact hle.trans inf_le_right

/-- A Borel two-actor calculation on the original quotient proves (2B),
including central scalar covers. -/
theorem remainder_le_kernel_of_borel_two_inner (i : Fin 2)
    (A : Subgroup (X ⧸ Q.D))
    (hn : Q.tits.standardParabolic {Q.simple i} ≤ normalizer (A : Set (X ⧸ Q.D)))
    (hgen : A ⊔ Q.tits.B = Q.tits.standardParabolic {Q.simple i})
    (T : Sylow 2 A) (hTU : (T : Subgroup A).map A.subtype ≤ split.U)
    (hNB : ((normalizer (((T : Subgroup A).map (QuotientGroup.mk' (pCore 2 A))) :
        Set (A ⧸ pCore 2 A))).comap (QuotientGroup.mk' (pCore 2 A))).map A.subtype ≤ Q.tits.B)
    (hi : BorelTwoInner
      ((T : Subgroup A).map (QuotientGroup.mk' (pCore 2 A)))
      (normalizer (((T : Subgroup A).map (QuotientGroup.mk' (pCore 2 A))) : Set _)))
    (hc : Nat.card (simpleRoot Q split i) =
      Nat.card ((T : Subgroup A).map (QuotientGroup.mk' (pCore 2 A)))) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  let M := Q.tits.standardParabolic {Q.simple i}
  let R := LocalCover.radical Q split i
  let S := (T : Subgroup A).map A.subtype
  let q := QuotientGroup.mk' (pCore 2 A)
  let Tbar := (T : Subgroup A).map q
  have hUM : split.U ≤ M := split.U_le.trans (Q.tits.B_le_standardParabolic _)
  have hUA : split.U ≤ normalizer (A : Set (X ⧸ Q.D)) := hUM.trans hn
  have hinner := borel_two_inner_action Q split i A hn T hTU hNB hi
  let f : split.U →* MulAut (A ⧸ pCore 2 A) :=
    (pCoreJoinAction 2 hUA).comp (inclusion le_sup_right)
  have hAR : A.pCoreIn 2 ≤ R := by
    have hAU : A.pCoreIn 2 ≤ split.U := (pCoreIn_le_sylow A T).trans hTU
    apply le_inf hAU
    have hMA := hn.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
    let : ((A.pCoreIn 2).subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMA
    have hcore : (A.pCoreIn 2).subgroupOf M ≤ (Q.tits.B.subgroupOf M).normalCore :=
      normal_le_normalCore.mpr (subgroupOf_mono _ (hAU.trans split.U_le))
    intro x hx
    exact ⟨⟨x,hUM (hAU hx)⟩,hcore hx,rfl⟩
  have hSR : S ⊔ R = split.U := by
    apply le_antisymm (sup_le hTU inf_le_left)
    intro u hu
    obtain ⟨_,⟨t,ht,rfl⟩,he⟩ := hinner ⟨u,hu⟩
    change MulAut.conj (q t) = f ⟨u,hu⟩ at he
    let tu : split.U := ⟨t,hTU (mem_map_of_mem A.subtype ht)⟩
    have hft : f tu = MulAut.conj (q t) := pCoreJoinAction_on_component 2 hUA t
    have hk : pCoreJoinAction 2 hUA (inclusion le_sup_right (tu⁻¹ * ⟨u,hu⟩)) = 1 := by
      change f (tu⁻¹ * ⟨u,hu⟩) = 1
      rw [map_mul,map_inv,hft,he,inv_mul_cancel]
    have hcB : A.pCoreIn 2 ≤ Q.tits.B :=
      (pCoreIn_le_sylow A T).trans (hTU.trans split.U_le)
    let ku : split.U := tu⁻¹ * ⟨u,hu⟩
    have hkpoint (a : A) : q (A.normalizerMonoidHom ⟨ku,hUA ku.property⟩ a) = q a := by
      have hh := DFunLike.congr_fun hk (q a)
      rw [pCoreJoinAction_mk] at hh
      exact hh
    have hkK := action_kernel_le_panel Q split i A hn hgen hcB hUA ku hkpoint
    have hkR : (t : X ⧸ Q.D)⁻¹ * u ∈ R :=
      ⟨split.U.mul_mem (split.U.inv_mem tu.property) hu,hkK⟩
    have hsm := (S ⊔ R).mul_mem
      (mem_sup_left (mem_map_of_mem A.subtype ht)) (mem_sup_right hkR)
    change (t : X ⧸ Q.D) * ((t : X ⧸ Q.D)⁻¹ * u) ∈ S ⊔ R at hsm
    rw [mul_inv_cancel_left] at hsm
    exact hsm
  exact remainder_le_kernel_of_sylow_supplement Q split i A T hTU hSR hAR hc

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel
