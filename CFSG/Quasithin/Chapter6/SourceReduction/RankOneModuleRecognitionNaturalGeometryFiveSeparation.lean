module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveFixedOrbit
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.Commutator.FixedPointFree

/-!
# The cubic and the full ambient S5 natural span

The cubic norm on an elementary abelian group is a homomorphism. It
vanishes on the original natural layer, where the cubic is fixed-free.
It also vanishes on each conjugate by C_K(c), since these conjugators
commute with the cubic. The proved equality of the C_K(c)-span and the
K-span therefore makes the cubic fixed-free on the whole ambient span.
Its commutator map is surjective, giving the literal full commutator.

The cubic-fixed two-core already centralizes this span. Its intersection
with the span is now trivial, so multiplication gives an actual direct
product inside their join. In the contained S5 branch, the fixed-core
involution forced by generation one lies outside this entire span. This
retains the original extension kernel rather than replacing the ambient
cover by its faithful action. The final theorem keeps the same W/Z_S
witness and all its specified quotient maps.

S5 parabolic escape, the mixed-amalgam contradiction, initial 6.1.4–5,
omega escape and unconditional 6.1.27 remain with
qt-d-1222-rankone-recognition-natural. No elementary lift is asserted.
Source: Aschbacher–Smith 6.1.19, printed p.675 (`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private theorem cubic_fixed_span
    {G : Type*} [Group G] (V C : Subgroup G) (c : G)
    (hcV : c ∈ normalizer (V : Set G)) (hc3 : c^3=1)
    (hCc : C ≤ centralizer (zpowers c : Set G))
    (hfree : ∀ v ∈ V, c*v*c⁻¹=v → v=1)
    [IsElementaryAbelian 2 (conjugateSpanBy V C)] :
    conjugateSpanBy V C ⊓ centralizer (zpowers c : Set G) = ⊥ := by
  let S := conjugateSpanBy V C
  let : CommGroup S := IsMulCommutative.instCommGroup
  have hcC : c ∈ normalizer (C : Set G) := by
    apply Subgroup.centralizer_le_normalizer (C : Set G)
    intro x hx
    exact (hCc hx c (mem_zpowers c)).symm
  have hcS : c ∈ normalizer (S : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,map_conjugateSpanBy,
      mem_normalizer_iff_map_conj_eq.mp hcV,
      mem_normalizer_iff_map_conj_eq.mp hcC]
  let a := S.normalizerMonoidHom ⟨c,hcS⟩
  have ha3 : a^3=1 := by
    rw [←map_pow]
    have hh : (⟨c,hcS⟩ : normalizer (S : Set G))^3=1 := Subtype.ext hc3
    rw [hh,map_one]
  have haaa (x : S) : a (a (a x))=x := by
    simpa only [pow_succ,pow_zero,one_mul,MulAut.mul_apply,MulAut.one_apply] using
      DFunLike.congr_fun ha3 x
  let f : S →* S := {
    toFun x := x * a x * a (a x)
    map_one' := by simp
    map_mul' x y := by simp only [map_mul]; ac_rfl }
  have hfix (x : S) : a (f x)=f x := by
    change a (x*a x*a (a x))=x*a x*a (a x)
    rw [map_mul,map_mul,haaa]
    ac_rfl
  have hvnorm (v : G) (hv : v ∈ V) :
      f ⟨v,le_conjugateSpanBy V C hv⟩=1 := by
    apply Subtype.ext
    apply hfree
    · exact V.mul_mem (V.mul_mem hv ((mem_normalizer_iff.mp hcV v).mp hv))
        ((mem_normalizer_iff.mp hcV _).mp ((mem_normalizer_iff.mp hcV v).mp hv))
    · exact congrArg Subtype.val (hfix ⟨v,le_conjugateSpanBy V C hv⟩)
  have hle : S ≤ f.ker.map S.subtype := by
    apply (closure_le _).mpr
    rintro _ ⟨d,hd,v,hv,rfl⟩
    let b := S.normalizerMonoidHom ⟨d,le_normalizer_conjugateSpanBy V C hd⟩
    have hcd : c*d=d*c := hCc hd c (mem_zpowers c)
    have hab (x : S) : a (b x)=b (a x) := by
      apply Subtype.ext
      change c*(d*(x : G)*d⁻¹)*c⁻¹=d*(c*(x : G)*c⁻¹)*d⁻¹
      calc
        _ = (c*d)*(x : G)*(c*d)⁻¹ := by group
        _ = (d*c)*(x : G)*(d*c)⁻¹ := by rw [hcd]
        _ = _ := by group
    have hfb (x : S) : f (b x)=b (f x) := by
      change b x*a (b x)*a (a (b x))=b (x*a x*a (a x))
      simp only [hab,map_mul]
    refine ⟨b ⟨v,le_conjugateSpanBy V C hv⟩,?_,rfl⟩
    change f (b ⟨v,le_conjugateSpanBy V C hv⟩)=1
    rw [hfb,hvnorm v hv,map_one]
  apply bot_unique
  intro x hx
  have hfx : f ⟨x,hx.1⟩=1 := by
    obtain ⟨y,hy,he⟩ := hle hx.1
    have hyx : y=⟨x,hx.1⟩ := Subtype.ext he
    exact hyx ▸ hy
  have hax : a ⟨x,hx.1⟩=⟨x,hx.1⟩ := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2 c (mem_zpowers c))
  have hx2 : (⟨x,hx.1⟩ : S)^2=1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 S) _
  change (⟨x,hx.1⟩ : S)*a ⟨x,hx.1⟩*a (a ⟨x,hx.1⟩)=1 at hfx
  rw [hax,hax,←pow_two,hx2,one_mul] at hfx
  exact congrArg Subtype.val hfx

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

/-- The original cubic is fixed-free on the entire abelian natural-layer
span of the same S5 cover, not only on its seed and central line. -/
theorem natural_five_span_cubic_fixed_eq_bot
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    conjugateSpanBy (layer L R) K ⊓ centralizer (zpowers c : Set G) = ⊥ := by
  let V := layer L R
  let S := conjugateSpanBy V K
  have hSU : S ≤ Escape.U (T : Subgroup G) L R := by
    have he : conjugateSpanBy V (Escape.I (T : Subgroup G) L R) =
        Escape.U (T : Subgroup G) L R := by
      rw [conjugateSpanBy_eq_iSup_conj]
      rfl
    rw [←he]
    exact conjugateSpanBy_mono le_rfl hKI
  let := h.layer_elementary
  let : IsMulCommutative S := le_centralizer_iff_isMulCommutative.mp
    (hSU.trans (hab.trans (centralizer_le hSU)))
  let : IsElementaryAbelian 2 S := conjugateSpanBy_elementary_of_commutative _ _
  have heq := natural_five_fixed_span_eq h hnat K hKI hNK e hcL hcN hc3
  let : IsElementaryAbelian 2
      (conjugateSpanBy V (K ⊓ centralizer (zpowers c : Set G))) := by
    change IsElementaryAbelian 2 (conjugateSpanBy (layer L R)
      (K ⊓ centralizer (zpowers c : Set G)))
    rw [heq]
    infer_instance
  rw [←heq]
  exact cubic_fixed_span V _ c (normalizer_commutator_ge_right R L hcL)
    (hc3 ▸ pow_orderOf_eq_one c) inf_le_right
    (fun _ hv hfix => hnat.cubic_fixed_eq_one hcL hc3 hv hfix)

/-- The actual cubic-fixed two-core is disjoint from the whole natural
span. Its earlier nontrivial involution therefore survives beyond this span. -/
theorem natural_five_fixed_core_span_disjoint
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    Disjoint ((Escape.H (T : Subgroup G) L R).pCoreIn 2 ⊓
      centralizer (zpowers c : Set G)) (conjugateSpanBy (layer L R) K) := by
  apply disjoint_iff.mpr
  apply bot_unique
  exact (inf_le_inf_right _ inf_le_right).trans_eq
    ((inf_comm _ _).trans (natural_five_span_cubic_fixed_eq_bot h hnat K hKI hNK e hab hcL hcN hc3))

/-- Multiplication gives the actual direct product of the fixed two-core
and the natural span inside their ambient join, with both embeddings retained. -/
theorem natural_five_fixed_core_span_product
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    let D := (Escape.H (T : Subgroup G) L R).pCoreIn 2 ⊓ centralizer (zpowers c : Set G)
    let S := conjugateSpanBy (layer L R) K
    ∃ b : D × S ≃* (D ⊔ S : Subgroup G), ∀ d s, (b (d,s) : G) = (d : G)*(s : G) :=
  exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _
    (natural_five_fixed_core_span_disjoint h hnat K hKI hNK e hab hcL hcN hc3)
    (natural_five_fixed_core_centralizes_span h hnat K hKI hNK e hcL hcN hc3)

/-- The same cubic moves the entire span: the commutator subgroup is
computed inside the original ambient group. -/
theorem natural_five_span_cubic_commutator
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    ⁅conjugateSpanBy (layer L R) K,zpowers c⁆ = conjugateSpanBy (layer L R) K := by
  have hcS : c ∈ normalizer (conjugateSpanBy (layer L R) K : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,map_conjugateSpanBy,
      mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_right R L hcL),
      mem_normalizer_iff_map_conj_eq.mp (hNK hcN)]
  apply commutator_eq_of_fixedPointFree _ _ (zpowers_le.mpr hcS) c (mem_zpowers c)
  intro v hv hcv
  apply mem_bot.mp
  rw [←natural_five_span_cubic_fixed_eq_bot h hnat K hKI hNK e hab hcL hcN hc3]
  refine ⟨hv,?_⟩
  intro x hx
  obtain ⟨m,rfl⟩ := hx
  exact hcv.zpow_left m

/-- The original cubic separates its fixed two-core from the natural
span, with a literal commutator identity and multiplication equivalence. -/
@[expose] def NaturalFiveSpanSeparationData (T : Sylow 2 G) (L R K : Subgroup G) : Prop :=
  let S := conjugateSpanBy (layer L R) K
  ∀ _e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5),
    ∀ c : G, c ∈ L → c ∈ Escape.H (T : Subgroup G) L R → orderOf c=3 →
      S ⊓ centralizer (zpowers c : Set G) = ⊥ ∧ ⁅S,zpowers c⁆ = S ∧
      let D := (Escape.H (T : Subgroup G) L R).pCoreIn 2 ⊓ centralizer (zpowers c : Set G)
      ∃ b : D × S ≃* (D ⊔ S : Subgroup G), ∀ d s, (b (d,s) : G) = (d : G)*(s : G)

/-- Package the separation for every marking of the same original cover. -/
theorem natural_five_span_separation_data
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    NaturalFiveSpanSeparationData T L R K := by
  intro e c hcL hcN hc3
  exact ⟨natural_five_span_cubic_fixed_eq_bot h hnat K hKI hNK e hab hcL hcN hc3,
    natural_five_span_cubic_commutator h hnat K hKI hNK e hab hcL hcN hc3,
    natural_five_fixed_core_span_product h hnat K hKI hNK e hab hcL hcN hc3⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d
/-- The original W/Z_S witness retains the fixed-free cubic action on
its entire natural span. The nontrivial fixed-core involution lies outside
that span, and multiplication realizes the actual direct product. -/
theorem exists_ambient_amalgam_or_five_separated_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let N := Escape.H (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N) (_hIN : I ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      let := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        let := hX
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Bijective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧ g.ker = pCore 2 P ∧
            (Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5))) ∧
            ((pResidual 2 P).map P.subtype = (primeToResidual 3 I).map I.subtype) ∧
            (N ≤ Subgroup.normalizer ((pResidual 2 P).map P.subtype : Set G)) ∧
            NaturalInvariantCoverData T P I N σ hPI ∧
            NaturalEscapingCoverData T P N M ∧
            NaturalFiveCubicParabolicData T L R P N ∧
            NaturalThreeInvariantParabolicData T L R P N M ∧
            (NaturalEscapingAmalgamData T L R P N M ∨
              (NaturalFiveContainedParabolicData T P N M ∧
                NaturalFiveElementaryRestriction P N ∧
                NaturalFiveCubicFixedData T L R P N ∧
                NaturalFiveSpanActionData T L R (P ⊔ N.pCoreIn 2) ∧
                NaturalFiveFixedOrbitData T L R (P ⊔ N.pCoreIn 2) M ∧
                NaturalFiveSpanSeparationData T L R (P ⊔ N.pCoreIn 2) ∧
                ∃ c t : G, c ∈ L ∧ c ∈ N ∧ orderOf c=3 ∧
                  t ∈ N.pCoreIn 2 ∧ orderOf t=2 ∧ c*t*c⁻¹=t ∧ t ∉ Z ∧ t ∉ conjugateSpanBy (layer L R) (P ⊔ N.pCoreIn 2) ∧
                  t ∈ centralizer (layer L R : Set G) ∧
                  t ∈ centralizer (conjugateSpanBy (layer L R)
                    ((P ⊔ N.pCoreIn 2) ⊓ centralizer (zpowers c : Set G)) : Set G))) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,ham⟩ :=
    d.exists_ambient_amalgam_or_five_fixed_orbit h hnat hE hs hNS hab
  let := hZ
  let := hX
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,?_⟩
  apply ham.imp_right
  rintro ⟨hd,hno,hfixed,hspan,horbit,c,t,hcL,hcN,hc3,ht,ht2,hct,htZ,htV,htS⟩
  have hsep := natural_five_span_separation_data (hn ▸ h) (hn ▸ hnat) _ hcover.1 hcover.2.1 hab
  refine ⟨hd,hno,hfixed,hspan,horbit,hsep,c,t,hcL,hcN,hc3,ht,ht2,hct,htZ,?_,htV,htS⟩
  intro htspan
  obtain ⟨_,_,_,_,⟨eK⟩,_⟩ := hcover
  have hzero := (hsep (eK.trans hd.1.some) c hcL hcN hc3).1
  have htc : t ∈ centralizer (zpowers c : Set G) := by
    intro x hx
    have hc : c ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hct)
    exact mem_centralizer_singleton_iff.mp (zpowers_le.mpr hc hx)
  have htone : t=1 := mem_bot.mp (hzero ▸ (show t ∈
    conjugateSpanBy (layer L R) (_ ⊔ (Escape.H (T : Subgroup G) L R).pCoreIn 2) ⊓
      centralizer (zpowers c : Set G) from ⟨htspan,htc⟩))
  rw [htone,orderOf_one] at ht2
  omega
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
