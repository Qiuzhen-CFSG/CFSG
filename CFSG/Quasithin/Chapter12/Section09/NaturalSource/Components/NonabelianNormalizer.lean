module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianLift
public import Theory.SpecificGroups.SymmetricEight.FourBlockSylowResidual
public import Theory.GroupTheory.PResidual.IndexThree

/-!
# Normalizing the original plane-centralizer residual

The dotted plane-point parabolic has order 576, and its intersection with
the seed stabilizer is the original dotted L₀T of order 192. The faithful
point-component quotient puts the kernel on K₁T inside T, so these orders
lift to the literal index-three relation L₀T ≤ P, where P is the restricted
component parabolic. The general index-three residual lemma and
O²(L₀T) = L₀ therefore show that P normalizes the original L₀.

The same P preserves I and V₂I. It consequently preserves the L₀-fixed
extension V₂C_I(L₀). If C_I(L₀) were trivial, P would preserve V₂,
contradicting the already proved parabolic movement. The final application
constructs these data on the same original flag and natural constituent.
The guarded earlier module theorem and NaturalReduction 4 remain explicit.

This proves the normalizer and nonzero fixed-subgroup step. The fixed-space
identification and final ambient contradiction remain with source assembly;
no equality between C_I(Z(U)^g) and [I,Z(U)^g] is assumed.

Source: Aschbacher--Smith, proof of 12.9.4, printed pp.859--860 of
refs/quasithin.pdf, with the parabolic lifted inside the original K₁T.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem dot_sylow_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    Nat.card (F.terminalDot (T : Subgroup G)) = 64 := by
  obtain ⟨e⟩ := nonabelian_caseFive_alternating_eight h (.inl rfl) earlier F hne B h5
  have hc : Nat.card F.TerminalHdot = 20160 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  let Q := (T.subtype (F.invariant 1)).mapSurjective
    (f := QuotientGroup.mk' F.terminalHatAction.ker) (QuotientGroup.mk'_surjective _)
  change Nat.card Q = 64
  rw [Q.card_eq_multiplicity,hc,show 20160 = 2^6*315 from rfl,
    Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]

/-- The full dotted point parabolic has its original orthogonal-model order. -/
theorem nonabelian_caseFive_planePoint_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    Nat.card (F.terminalPointCentralizer v) = 576 := by
  obtain ⟨q,c,e,he⟩ := nonabelian_caseFive_marking h (.inl rfl) earlier F hne B h5
  let Q := (T.subtype (F.invariant 1)).mapSurjective
    (f := QuotientGroup.mk' F.terminalHatAction.ker) (QuotientGroup.mk'_surjective _)
  let et : F.TerminalHdot ≃* (⊤ : Subgroup F.TerminalHdot) := topEquiv.symm
  let Qt : Sylow 2 (⊤ : Subgroup F.TerminalHdot) :=
    Q.mapSurjective (f := et.toMonoidHom) et.surjective
  let a : (⊤ : Subgroup F.TerminalHdot) ≃* alternatingGroup (Fin 8) := topEquiv.trans e
  have ha : ∀ (x : (⊤ : Subgroup F.TerminalHdot)) (u : F.Uhat),
      c (Additive.ofMul (F.terminalFaithfulHatAction x u)) =
        BinaryPermutation.naturalRepresentation (Fin 8) (a x).val (c (Additive.ofMul u)) :=
    fun x u => he x (Additive.ofMul u)
  have hfix : ∀ x ∈ (Qt : Subgroup (⊤ : Subgroup F.TerminalHdot)),
      F.terminalFaithfulHatAction x v.toMul = v.toMul := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact sylow_fixes_plane_hat_point F v hv hline y hy
  obtain ⟨_,s,_,_,⟨r⟩,_⟩ := F.terminal_alternating_eight_residual_rank
    q c ⊤ a ha Qt v.toMul hv hfix
  let P := F.terminalPointCentralizer v
  have hs : Nat.card P = Nat.card BinaryPermutation.TerminalOrthogonal.FourBlockResidual.P := by
    rw [←Nat.card_congr s.toEquiv]
    exact (Nat.card_congr (subgroupOfEquivOfLe (show P ≤ ⊤ from le_top)).toEquiv).symm
  have hd1 : Nat.card P ∣ 1152 := by
    rw [hs]
    exact (card_dvd_of_le (show BinaryPermutation.TerminalOrthogonal.FourBlockResidual.P ≤
      Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.fourStabilizer from inf_le_right)).trans
      (dvd_of_eq Theory.SpecificGroups.SymmetricEight.FourBlockSylowResidual.fourStabilizer_card)
  have hd2 : Nat.card P ∣ 20160 := by
    have hh := P.card_subgroup_dvd_card
    have hc : Nat.card F.TerminalHdot = 20160 := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]; rfl
    rwa [hc] at hh
  have hupper : Nat.card P ∣ 576 := by
    simpa only [show Nat.gcd 1152 20160 = 576 from rfl] using Nat.dvd_gcd hd1 hd2
  have h64 : 64 ∣ Nat.card P := by
    rw [←dot_sylow_card h earlier F hne B h5]
    exact card_dvd_of_le (sylow_fixes_plane_hat_point F v hv hline)
  have h144 : 144 ∣ Nat.card P := by
    have hc : Nat.card (primeToResidual 3 ((F.terminalPointStabilizer v.toMul).subgroupOf ⊤)) = 144 :=
      (Nat.card_congr r.toEquiv).trans BinaryPermutation.TerminalOrthogonal.FourBlockResidual.product_card
    rw [←hc]
    have hd := (primeToResidual 3 ((F.terminalPointStabilizer v.toMul).subgroupOf ⊤)).card_subgroup_dvd_card
    exact hd.trans (dvd_of_eq (Nat.card_congr
      (subgroupOfEquivOfLe (show P ≤ ⊤ from le_top)).toEquiv))
  have hlower : 576 ∣ Nat.card P := by
    simpa only [show Nat.lcm 64 144 = 576 from rfl] using Nat.lcm_dvd h64 h144
  exact Nat.dvd_antisymm hupper hlower

private theorem seed_point_index_le_eight
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    (F.terminalPointCentralizer v).relIndex
      (F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G))) ≤ 8 := by
  let P := F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G))
  let W := hatSpace F V
  have hp := (nonabelian_caseFive_seed_stabilizer h (.inl rfl) earlier F hne g hgP hgH B h5).1
  let : MulAction P (Additive F.Uhat) := {
    smul a w := F.terminalRepresentation a w
    one_smul w := by change F.terminalRepresentation 1 w = w; rw [map_one]; rfl
    mul_smul a b w := by change F.terminalRepresentation (a*b) w = _; rw [map_mul]; rfl }
  have hvW : v ∈ W := by
    have hvline : v ∈ hatSpace F (F.Vi 2) := by
      rw [hline]
      exact Submodule.mem_span_singleton_self v
    change v.toMul ∈ hatImage F V
    exact (map_mono (comap_mono (F.le_seed 2))) hvline
  have horbit : ∀ w ∈ MulAction.orbit P v, w ∈ W := by
    intro w hw
    obtain ⟨a,rfl⟩ := MulAction.mem_orbit_iff.mp hw
    exact ((show (a:F.TerminalHdot) ∈ BinaryOffender.subspaceStabilizer
      F.terminalRepresentation W from hp ▸ a.property) v).mpr hvW
  let j : MulAction.orbit P v → W := fun w => ⟨w,horbit w w.property⟩
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (congrArg (fun w : W => (w : Additive F.Uhat)) he)
  have hstab : (F.terminalPointCentralizer v).subgroupOf P = MulAction.stabilizer P v := rfl
  change ((F.terminalPointCentralizer v).subgroupOf P).index ≤ 8
  rw [hstab,MulAction.index_stabilizer,←Nat.card_coe_set_eq]
  apply (Nat.card_le_card_of_injective j hj).trans_eq
  obtain ⟨_,he,hd⟩ := nonabelian_caseFive_seed_intersection h (.inl rfl) earlier F hne g hgP hgH B h5
  have hdim : finrank (ZMod 2) W = 3 := by
    change finrank (ZMod 2) (hatSpace F V) = 3
    rwa [he] at hd
  let : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),hdim,Nat.card_zmod]
  rfl

/-- The original dotted L₀T is the order-192 intersection of the two parabolics. -/
theorem nonabelian_caseFive_planeResidual_dot_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    Nat.card (F.terminalDot (planeCentralizerResidual F L) ⊔ F.terminalDot (T : Subgroup G) :
      Subgroup F.TerminalHdot) = 192 := by
  rw [nonabelian_planeResidual_dot_intersection h earlier F hne v hv hline]
  let P := F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G))
  let Q := F.terminalPointCentralizer v
  have hp := nonabelian_caseFive_seed_stabilizer_card h (.inl rfl) earlier F hne g hgP hgH B h5
  have hq := nonabelian_caseFive_planePoint_card h earlier F hne B h5 v hv hline
  have hd : Nat.card (P ⊓ Q : Subgroup F.TerminalHdot) ∣ 192 := by
    have hh := Nat.dvd_gcd (card_dvd_of_le (show P ⊓ Q ≤ P from inf_le_left))
      (card_dvd_of_le (show P ⊓ Q ≤ Q from inf_le_right))
    rw [hp,hq] at hh
    exact hh
  have hi : (P ⊓ Q).relIndex P ≤ 8 := by
    rw [inf_relIndex_left]
    exact seed_point_index_le_eight h earlier F hne g hgP hgH B h5 v hline
  have hm : Nat.card (P ⊓ Q : Subgroup F.TerminalHdot) * (P ⊓ Q).relIndex P = 1344 := by
    have hh := ((P ⊓ Q).subgroupOf P).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show P ⊓ Q ≤ P from inf_le_left)).toEquiv] at hh
    exact hh.trans hp
  have hlow : 168 ≤ Nat.card (P ⊓ Q : Subgroup F.TerminalHdot) := by
    have hh := Nat.mul_le_mul_left (Nat.card (P ⊓ Q : Subgroup F.TerminalHdot)) hi
    rw [hm] at hh
    omega
  have hhigh := Nat.le_of_dvd (by decide : 0 < 192) hd
  obtain ⟨k,hk⟩ := hd
  have hkbound := Nat.mul_le_mul_right k hlow
  rw [←hk] at hkbound
  have hk1 : k = 1 := by
    have hkne : k ≠ 0 := by intro he; simp [he] at hk
    omega
  simpa only [hk1,mul_one] using hk.symm


/-- The faithful dotted quotient has a two-group kernel on the original K₁T.
In particular that entire kernel lies in the original Sylow subgroup. -/
theorem nonabelian_caseFive_component_join_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) :
    (C.K1 ⊔ (T : Subgroup G)) ⊓ F.terminalHatAction.ker.map F.H.subtype ≤ (T : Subgroup G) := by
  let X := C.K1 ⊔ (T : Subgroup G)
  have hXH : X ≤ F.H := sup_le C.point_le (F.invariant 1)
  let N := C.K1.subgroupOf X
  let f : X →* F.TerminalHdot :=
    (QuotientGroup.mk' F.terminalHatAction.ker).comp (inclusion hXH)
  let S : Sylow 2 X := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (hXH.trans ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal))
  have hs : N ⊔ (T : Subgroup G).subgroupOf X = ⊤ := by
    rw [←subgroupOf_sup (show C.K1 ≤ X from le_sup_left)
      (show (T : Subgroup G) ≤ X from le_sup_right)]
    exact subgroupOf_self X
  have hquot : IsPGroup 2 (X ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N _ T.isPGroup'.comap_subtype hs
  obtain ⟨e,he⟩ := nonabelian_caseFive_point_core_equiv h earlier F hne B h5 C
  have hk (x : X) (hx : x ∈ N) (hfx : f x = 1) :
      (⟨(x:G),hx⟩ : C.K1) ∈ pCore 2 C.K1 := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    let k : C.K1 := ⟨x, show (x : G) ∈ C.K1 from hx⟩
    change e (QuotientGroup.mk' (pCore 2 C.K1) k) = e 1
    rw [he,e.map_one]
    exact hfx
  let a : f.ker →* (X ⧸ N) := (QuotientGroup.mk' N).comp f.ker.subtype
  have hzN (z : a.ker) : z.val.val ∈ N := by
    apply (QuotientGroup.eq_one_iff (N := N) z.val.val).mp
    exact z.property
  have hak : IsPGroup 2 a.ker := by
    let j : a.ker →* pCore 2 C.K1 := {
      toFun z := ⟨⟨(z.val.val:G),show (z.val.val:G) ∈ C.K1 from hzN z⟩,
        hk z.val.val (hzN z) z.val.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact pCore_isPGroup.of_injective j (by
      intro x y heq
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : pCore 2 C.K1 => (z.val:G)) heq)
  have hker : IsPGroup 2 f.ker := by
    have hp := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup a hak
    simpa using hp.of_equiv Subgroup.topEquiv
  have hkerS := hker.le_sylow_of_normal S
  rintro x ⟨hx,hh⟩
  obtain ⟨y,hy,hyx⟩ := hh
  have hfx : f ⟨x,hx⟩ = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (show y = inclusion hXH ⟨x,hx⟩ from Subtype.ext hyx) ▸ hy
  exact hkerS hfx


/-- The literal L₀T has index three in the restricted parabolic, with the
full dotted image and original Sylow retained. -/
theorem nonabelian_caseFive_component_plane_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    (planeCentralizerResidual F L ⊔ (T : Subgroup G)).relIndex
      (componentPlanePreimage F C v) = 3 := by
  let X := C.K1 ⊔ (T : Subgroup G)
  let A := planeCentralizerResidual F L ⊔ (T : Subgroup G)
  let P := componentPlanePreimage F C v
  have hXH : X ≤ F.H := sup_le C.point_le (F.invariant 1)
  have hAP : A ≤ P := componentPlanePreimage_contains F C v hv hline
  have hPX : P ≤ X := inf_le_left
  have hAX := hAP.trans hPX
  let f : X →* F.TerminalHdot :=
    (QuotientGroup.mk' F.terminalHatAction.ker).comp (inclusion hXH)
  have hkA : f.ker ≤ A.subgroupOf X := by
    intro x hx
    apply mem_sup_right
    apply nonabelian_caseFive_component_join_kernel h earlier F hne B h5 C
    exact ⟨x.property,⟨inclusion hXH x,(QuotientGroup.eq_one_iff _).mp hx,rfl⟩⟩
  have hkP : f.ker ≤ P.subgroupOf X := hkA.trans (comap_mono hAP)
  have image (Y : Subgroup G) (hYX : Y ≤ X) :
      (Y.subgroupOf X).map f = F.terminalDot Y := by
    ext y
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨inclusion hXH a,ha,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,hYX ha⟩,ha,rfl⟩
  have hi : A.relIndex P = (F.terminalDot A).relIndex (F.terminalDot P) := by
    rw [←image A hAX,←image P hPX,relIndex_map_map,
      sup_eq_left.mpr hkA,sup_eq_left.mpr hkP]
    have hh := relIndex_map_map_of_injective (A.subgroupOf X) (P.subgroupOf X) X.subtype_injective
    rwa [map_subgroupOf_eq_of_le hAX,map_subgroupOf_eq_of_le hPX] at hh
  have hRH : planeCentralizerResidual F L ≤ F.H := by
    rw [planeCentralizerResidual_eq_point F L]
    exact (map_subtype_le _).trans (inf_le_left.trans ((F.Li_le L 1).trans inf_le_right))
  have hdot : F.terminalDot A = F.terminalDot (planeCentralizerResidual F L) ⊔
      F.terminalDot (T : Subgroup G) := by
    change ((planeCentralizerResidual F L ⊔ (T : Subgroup G)).subgroupOf F.H).map _ = _
    rw [subgroupOf_sup hRH (F.invariant 1),Subgroup.map_sup]
    rfl
  have hcA : Nat.card (F.terminalDot A) = 192 := by
    rw [hdot]
    exact nonabelian_caseFive_planeResidual_dot_card h earlier F hne g hgP hgH B h5 v hv hline
  have hcP : Nat.card (F.terminalDot P) = 576 := by
    rw [nonabelian_caseFive_componentPlanePreimage_dot h earlier F hne B h5 C v]
    exact nonabelian_caseFive_planePoint_card h earlier F hne B h5 v hv hline
  have hdotle : F.terminalDot A ≤ F.terminalDot P := map_mono (comap_mono hAP)
  have hm := ((F.terminalDot A).subgroupOf (F.terminalDot P)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hdotle).toEquiv,hcA,hcP] at hm
  change 192 * (F.terminalDot A).relIndex (F.terminalDot P) = 576 at hm
  rw [hi]
  omega

/-- The original L₀ is normal in the restricted lift of the full dotted
parabolic. This is ambient normality, before passing to any module action. -/
theorem nonabelian_caseFive_component_plane_normalizes_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    componentPlanePreimage F C v ≤ normalizer (planeCentralizerResidual F L : Set G) := by
  have hn : (T : Subgroup G) ≤ normalizer (planeCentralizerResidual F L : Set G) :=
    (le_inf le_sup_right (F.invariant 2)).trans (planeResidual_normalizer h earlier F)
  have he := embedded_pResidual_join_pGroup (planeCentralizerResidual F L) (T : Subgroup G)
    (isPPerfect_embedded_pResidual 2 _) T.isPGroup' hn
  rw [←he]
  exact normalizes_embedded_twoResidual_of_relIndex_three
    (componentPlanePreimage_contains F C v hv hline)
    (nonabelian_caseFive_component_plane_index h earlier F hne g hgP hgH B h5 C v hv hline)


omit [Finite G] in
private theorem centralizer_sup_fixed_factor (A I R : Subgroup G)
    (hIA : I ≤ normalizer (A : Set G)) (hAR : A ≤ centralizer (R : Set G)) :
    (A ⊔ I) ⊓ centralizer (R : Set G) = A ⊔ (I ⊓ centralizer (R : Set G)) := by
  apply le_antisymm
  · rintro x ⟨hx,hxc⟩
    have hm : x ∈ (A : Set G) * (I : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left A I hIA]
      exact hx
    obtain ⟨a,ha,i,hi,hei⟩ := hm
    have hic : i ∈ centralizer (R : Set G) := by
      have hc := (centralizer (R : Set G)).mul_mem
        ((centralizer (R : Set G)).inv_mem (hAR ha)) hxc
      simpa only [←hei,inv_mul_cancel_left] using hc
    exact hei ▸ mul_mem_sup ha ⟨hi,hic⟩
  · exact sup_le (le_inf le_sup_left hAR)
      (le_inf (inf_le_left.trans le_sup_right) inf_le_right)

omit [Finite G] in
/-- The L₀-fixed part of the elementary extension retains its original
plane factor. No equality involving the returning-center commutator is used. -/
theorem nonabelian_plane_extension_fixed_residual
    (F : InvariantFlag T V 4) {I : Subgroup G} (hiZ : I ≤ F.ZU) :
    (F.Vi 2 ⊔ I) ⊓ centralizer (planeCentralizerResidual F L : Set G) =
      F.Vi 2 ⊔ (I ⊓ centralizer (planeCentralizerResidual F L : Set G)) := by
  apply centralizer_sup_fixed_factor
  · exact (hiZ.trans ((centerIn_le_centralizer F.U).trans
      (centralizer_le ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))))).trans
        (Subgroup.centralizer_le_normalizer _)
  · exact le_centralizer_iff.mp ((map_subtype_le _).trans inf_le_right)

/-- The restricted parabolic preserves both the same L₀-fixed constituent
and its extension by V₂. Since it moves V₂, the constituent fixed subgroup
is nontrivial. -/
theorem nonabelian_caseFive_component_plane_fixed_nontrivial
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    {I : Subgroup G} (c : ChosenModule T C.K1 I) (hiZ : I ≤ F.ZU)
    (hi : I = ⁅F.ZU,C.K1⁆) :
    I ⊓ centralizer (planeCentralizerResidual F L : Set G) ≠ ⊥ ∧
      componentPlanePreimage F C v ≤ normalizer
        ((I ⊓ centralizer (planeCentralizerResidual F L : Set G) : Subgroup G) : Set G) ∧
      componentPlanePreimage F C v ≤ normalizer
        ((F.Vi 2 ⊔ (I ⊓ centralizer (planeCentralizerResidual F L : Set G)) : Subgroup G) : Set G) := by
  have hPR := nonabelian_caseFive_component_plane_normalizes_residual
    h earlier F hne g hgP hgH B h5 C v hv hline
  have hPI : componentPlanePreimage F C v ≤ normalizer (I : Set G) := by
    rw [hi]
    have hHZ : F.H ≤ normalizer (F.ZU : Set G) :=
      (le_normalizer_conjugateSpanBy V F.H).trans
        (normalizer_le_normalizer_characteristic_image F.U (center F.U))
    have hHK := (normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal
    intro a ha
    have haH := (planePointPreimage_le_H F v) ha.2
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hHZ haH),
      mem_normalizer_iff_map_conj_eq.mp (hHK haH)]
  have hPE := (componentPlanePreimage_normalizes_natural_extension
    h earlier F C v hv hline c hiZ hi).1
  have hPC := hPR.trans (normalizer_le_normalizer_centralizer _)
  have hPF := (le_inf hPI hPC).trans inf_normalizer_le_normalizer_inf
  have hPfixed := (le_inf hPE hPC).trans inf_normalizer_le_normalizer_inf
  rw [nonabelian_plane_extension_fixed_residual F hiZ] at hPfixed
  refine ⟨?_,hPF,hPfixed⟩
  intro hf
  rw [hf,sup_bot_eq] at hPfixed
  exact nonabelian_caseFive_componentPlanePreimage_not_le_plane h earlier F hne g hgP hgH
    B h5 C v hv hline hPfixed

/-- The same original flag supplies the ambient L₀-normalizer and a nonzero
L₀-fixed subgroup of the same natural constituent. The final fixed-space
identification and parabolic contradiction remain with source assembly. -/
theorem nonabelian_caseFive_natural_normalizer_geometry
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    ∃ (v : Additive F.Uhat) (C : ComponentGeometry F L) (I : Subgroup G)
      (c : ChosenModule T C.K1 I),
      v ≠ 0 ∧ hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
      NaturalModule c 4 ∧ I ≤ F.ZU ∧ I = ⁅F.ZU,C.K1⁆ ∧ Nat.card I = 16 ∧
      (planeCentralizerResidual F L ⊔ (T : Subgroup G)).relIndex
        (componentPlanePreimage F C v) = 3 ∧
      componentPlanePreimage F C v ≤ normalizer (planeCentralizerResidual F L : Set G) ∧
      I ⊓ centralizer (planeCentralizerResidual F L : Set G) ≠ ⊥ ∧
      componentPlanePreimage F C v ≤ normalizer
        ((I ⊓ centralizer (planeCentralizerResidual F L : Set G) : Subgroup G) : Set G) ∧
      componentPlanePreimage F C v ≤ normalizer
        ((F.Vi 2 ⊔ (I ⊓ centralizer (planeCentralizerResidual F L : Set G)) : Subgroup G) : Set G) := by
  obtain ⟨v,C,I,c,hv,hline,hnat,hiZ,hi,hcard,_⟩ :=
    nonabelian_caseFive_natural_component_parabolic_geometry modules h preferred earlier four
      F hne g hgP hgH B h5
  exact ⟨v,C,I,c,hv,hline,hnat,hiZ,hi,hcard,
    nonabelian_caseFive_component_plane_index h earlier F hne g hgP hgH B h5 C v hv hline,
    nonabelian_caseFive_component_plane_normalizes_residual
      h earlier F hne g hgP hgH B h5 C v hv hline,
    nonabelian_caseFive_component_plane_fixed_nontrivial
      h earlier F hne g hgP hgH B h5 C v hv hline c hiZ hi⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
