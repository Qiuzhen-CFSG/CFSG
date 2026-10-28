module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveSeparation
public import Theory.GroupTheory.MarkedSemidirectProduct

/-!
# The original span extension retracts onto the cubic centralizer

Let K be the invariant S5 cover containing O2(N), let S be its natural-layer
span and let C = C_K(c). The original core calculation puts S inside O2(K).
The cubic is fixed-free on S, so S and C are disjoint. Since C normalizes S,
multiplication gives their actual internal semidirect product. Its retraction
onto C has kernel S and preserves every specified K/O2(K) marking.

Every elementary subgroup of this join consequently retracts to an elementary
subgroup of the actual cubic centralizer with exactly the same S5 image.
The kernel on C is its intrinsic O2(C), embedded as C_{O2(K)}(c). Thus adding
the natural span does not remove the original fixed-core lifting obstruction.
The final application retains the same W/Z_S witness and quotient maps.

S5 parabolic escape, mixed-amalgam recognition, initial 6.1.4–5, omega escape
and the remaining geometry through unconditional 6.1.27 remain with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.19, printed p.675 (`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private theorem split_retraction {G : Type*} [Group G]
    (S C : Subgroup G) (hn : C ≤ normalizer (S : Set G)) (hd : Disjoint S C) :
    ∃ r : (S ⊔ C : Subgroup G) →* C,
      (∀ c : C, r (inclusion le_sup_right c)=c) ∧
      r.ker = S.subgroupOf (S ⊔ C) ∧
      (∀ x : (S ⊔ C : Subgroup G), (x : G)*(r x : G)⁻¹ ∈ S) := by
  let b := markedSemidirectEquiv (S ⊔ C) S C rfl hn hd
  let r : (S ⊔ C : Subgroup G) →* C := SemidirectProduct.rightHom.comp b.symm.toMonoidHom
  have hb (x : (S ⊔ C : Subgroup G)) :
      (x : G) = ((b.symm x).left : G)*((b.symm x).right : G) := by
    have hh := markedSemidirectEquiv_apply (S ⊔ C) S C rfl hn hd (b.symm x)
    change (b (b.symm x) : G) = _ at hh
    rwa [b.apply_symm_apply] at hh
  have hr (x : (S ⊔ C : Subgroup G)) : (x : G)*(r x : G)⁻¹ ∈ S := by
    rw [hb]
    change ((b.symm x).left : G)*((b.symm x).right : G)*((b.symm x).right : G)⁻¹ ∈ S
    simpa only [mul_inv_cancel_right] using (b.symm x).left.property
  refine ⟨r,?_,?_,hr⟩
  · intro c
    have hh : b (SemidirectProduct.inr c) = inclusion le_sup_right c := by
      apply Subtype.ext
      change (1 : G)*c=c
      exact one_mul _
    change (b.symm (inclusion le_sup_right c)).right=c
    rw [←hh,b.symm_apply_apply]
    rfl
  · ext x
    change r x=1 ↔ (x : G) ∈ S
    constructor
    · intro hx
      simpa only [hx,coe_one,inv_one,mul_one] using hr x
    · intro hx
      have hc : (r x : G) ∈ S := by
        have hh := S.mul_mem (S.inv_mem (hr x)) hx
        simpa only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hh
      exact Subtype.ext (hd.le_bot ⟨hc,(r x).property⟩)

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

/-- The span is inside the actual cover's two-core whenever the cover
contains the original normalizer two-core. -/
theorem natural_five_span_le_cover_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hQK : (Escape.H (T : Subgroup G) L R).pCoreIn 2 ≤ K) :
    conjugateSpanBy (layer L R) K ≤ K.pCoreIn 2 := by
  let I := Escape.I (T : Subgroup G) L R
  let N := Escape.H (T : Subgroup G) L R
  have hIN : I ≤ N := Subgroup.centralizer_le_normalizer _
  have hNI : N ≤ normalizer (I : Set G) := normalizer_le_normalizer_centralizer _
  have hSU : conjugateSpanBy (layer L R) K ≤ Escape.U (T : Subgroup G) L R := by
    have he : conjugateSpanBy (layer L R) I = Escape.U (T : Subgroup G) L R := by
      rw [conjugateSpanBy_eq_iSup_conj]
      rfl
    rw [←he]
    exact conjugateSpanBy_mono le_rfl hKI
  have hSQ : conjugateSpanBy (layer L R) K ≤ N.pCoreIn 2 :=
    hSU.trans ((natural_escape_core h hnat).1.trans (pCoreIn_mono_of_normalizes hIN hNI))
  exact (le_inf (hSQ.trans hQK) hSQ).trans (inf_pCoreIn_le_of_le 2 (hKI.trans hIN))

/-- An actual retraction onto the original cubic centralizer. Its kernel
is exactly the ambient span, and it preserves the specified S5 quotient. -/
theorem natural_five_span_retraction
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hQK : (Escape.H (T : Subgroup G) L R).pCoreIn 2 ≤ K)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    let S := conjugateSpanBy (layer L R) K
    let C := K ⊓ centralizer (zpowers c : Set G)
    let J := S ⊔ C
    ∃ (hJK : J ≤ K) (r : J →* C),
      (∀ d : C, r (inclusion le_sup_right d)=d) ∧
      r.ker = S.subgroupOf J ∧
      Function.Surjective r ∧
      ∀ x : J,
        e (QuotientGroup.mk' (pCore 2 K) (inclusion hJK x)) =
          e (QuotientGroup.mk' (pCore 2 K) (inclusion inf_le_left (r x))) := by
  let S := conjugateSpanBy (layer L R) K
  let C := K ⊓ centralizer (zpowers c : Set G)
  let J := S ⊔ C
  have hSQ := natural_five_span_le_cover_core h hnat K hKI hQK
  have hJK : J ≤ K := sup_le (hSQ.trans (pCoreIn_le 2 K)) inf_le_left
  have hCS : C ≤ normalizer (S : Set G) := inf_le_left.trans (le_normalizer_conjugateSpanBy _ _)
  have hd : Disjoint S C := by
    apply disjoint_iff.mpr
    apply bot_unique
    exact (inf_le_inf_left S (show C ≤ centralizer (zpowers c : Set G) from inf_le_right)).trans_eq
      (natural_five_span_cubic_fixed_eq_bot h hnat K hKI hNK e hab hcL hcN hc3)
  obtain ⟨r,hr,hker,hdecomp⟩ := split_retraction S C hCS hd
  refine ⟨hJK,r,hr,hker,?_,?_⟩
  · intro d
    exact ⟨inclusion le_sup_right d,hr d⟩
  · intro x
    apply congrArg e
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hh : inclusion hJK x / inclusion (show C ≤ K from inf_le_left) (r x) ∈
        (K.pCoreIn 2).comap K.subtype := by
      change (x : G) / (r x : G) ∈ K.pCoreIn 2
      simpa only [div_eq_mul_inv] using hSQ (hdecomp x)
    rw [pCoreIn,comap_map_eq_self_of_injective K.subtype_injective] at hh
    exact hh


/-- Adding the natural span produces no new elementary quotient images:
every one retracts to an elementary subgroup of the actual C_K(c). -/
theorem natural_five_span_elementary_retract
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hQK : (Escape.H (T : Subgroup G) L R).pCoreIn 2 ≤ K)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    let S := conjugateSpanBy (layer L R) K
    let C := K ⊓ centralizer (zpowers c : Set G)
    let J := S ⊔ C
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
    ∃ hJK : J ≤ K, ∀ A : Subgroup J, IsElementaryAbelian 2 A →
      ∃ A₀ : Subgroup K, A₀ ≤ (centralizer (zpowers c : Set G)).subgroupOf K ∧
        IsElementaryAbelian 2 A₀ ∧ A₀.map q = A.map (q.comp (inclusion hJK)) := by
  obtain ⟨hJK,r,_,_,_,he⟩ := natural_five_span_retraction h hnat K hKI hNK hQK e hab hcL hcN hc3
  refine ⟨hJK,?_⟩
  intro A hA
  let := hA
  let C := K ⊓ centralizer (zpowers c : Set G)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let j : C →* K := inclusion inf_le_left
  let A₀ := (A.map r).map j
  let : IsElementaryAbelian 2 (A.map r) := IsElementaryAbelian.map r
  refine ⟨A₀,?_,IsElementaryAbelian.map j,?_⟩
  · rintro x ⟨d,_,rfl⟩
    exact d.property.2
  · change ((A.map r).map j).map q = _
    rw [map_map,map_map]
    congr 1
    exact MonoidHom.ext (fun x => (he x).symm)

/-- The cubic centralizer has its own exact S5 quotient: the kernel of
the original marking restricted to it is its intrinsic two-core. -/
theorem natural_five_cubic_centralizer_kernel
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    let C := K ⊓ centralizer (zpowers c : Set G)
    let f := (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp
      (inclusion (show C ≤ K from inf_le_left))
    f.ker = pCore 2 C ∧
      C.pCoreIn 2 = K.pCoreIn 2 ⊓ centralizer (zpowers c : Set G) := by
  let C := K ⊓ centralizer (zpowers c : Set G)
  let j : C →* K := inclusion inf_le_left
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let f := q.comp j
  have hqk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hfk : f.ker = (pCore 2 K).comap j := by
    rw [←MonoidHom.comap_ker,hqk]
  have hp : IsPGroup 2 f.ker := hfk ▸ pCore_isPGroup.comap_of_injective j (inclusion_injective _)
  have hf : Function.Surjective f := natural_five_cubic_fixed_cover h hnat K hKI hNK e hcL hcN hc3
  have hk : f.ker = pCore 2 C := by
    have hh := f.comap_pCore_of_ker_isPGroup hf hp
    rwa [Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot,MonoidHom.comap_bot] at hh
  refine ⟨hk,?_⟩
  change (pCore 2 C).map C.subtype = _
  rw [←hk,hfk]
  apply le_antisymm
  · rintro x ⟨d,hd,rfl⟩
    exact ⟨⟨j d,hd,rfl⟩,d.property.2⟩
  · rintro x ⟨⟨k,hk,hkx⟩,hc⟩
    have hxK : x ∈ K := hkx ▸ k.property
    refine ⟨⟨x,hxK,hc⟩,?_,rfl⟩
    change j ⟨x,hxK,hc⟩ ∈ pCore 2 K
    have he : j ⟨x,hxK,hc⟩ = k := Subtype.ext hkx.symm
    rwa [he]

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

/-- Retraction and elementary-image transport in the original ambient
join, with the actual fixed two-core retained as the centralizer kernel. -/
@[expose] def NaturalFiveSpanRetractionData (T : Sylow 2 G) (L R K : Subgroup G) : Prop :=
  ∀ e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5),
  ∀ c : G, c ∈ L → c ∈ Escape.H (T : Subgroup G) L R → orderOf c=3 →
    let S := conjugateSpanBy (layer L R) K
    let C := K ⊓ centralizer (zpowers c : Set G)
    let J := S ⊔ C
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
    let f := q.comp (inclusion (show C ≤ K from inf_le_left))
    ∃ (hJK : J ≤ K) (r : J →* C),
      (∀ d : C, r (inclusion le_sup_right d)=d) ∧
      r.ker = S.subgroupOf J ∧ Function.Surjective r ∧
      (∀ x : J, q (inclusion hJK x) = f (r x)) ∧
      (∀ A : Subgroup J, IsElementaryAbelian 2 A →
        ∃ A₀ : Subgroup K, A₀ ≤ (centralizer (zpowers c : Set G)).subgroupOf K ∧
          IsElementaryAbelian 2 A₀ ∧ A₀.map q = A.map (q.comp (inclusion hJK))) ∧
      f.ker = pCore 2 C ∧
      C.pCoreIn 2 = K.pCoreIn 2 ⊓ centralizer (zpowers c : Set G)

/-- The original cover supplies the retraction without any splitting
assumption on its S5 extension or on the fixed two-core. -/
theorem natural_five_span_retraction_data
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hQK : (Escape.H (T : Subgroup G) L R).pCoreIn 2 ≤ K)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    NaturalFiveSpanRetractionData T L R K := by
  intro e c hcL hcN hc3
  obtain ⟨hJK,r,hr,hker,hsurj,he⟩ :=
    natural_five_span_retraction h hnat K hKI hNK hQK e hab hcL hcN hc3
  obtain ⟨hJK',hA⟩ := natural_five_span_elementary_retract h hnat K hKI hNK hQK e hab hcL hcN hc3
  exact ⟨hJK,r,hr,hker,hsurj,he,hA,
    natural_five_cubic_centralizer_kernel h hnat K hKI hNK e hcL hcN hc3⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d
/-- On the same original W/Z_S witness, elementary images in the span
extension retract to the actual cubic centralizer with its two-core kernel. -/
theorem exists_ambient_amalgam_or_five_retracted_core
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
                NaturalFiveSpanRetractionData T L R (P ⊔ N.pCoreIn 2) ∧
                ∃ c t : G, c ∈ L ∧ c ∈ N ∧ orderOf c=3 ∧
                  t ∈ N.pCoreIn 2 ∧ orderOf t=2 ∧ c*t*c⁻¹=t ∧ t ∉ Z ∧ t ∉ conjugateSpanBy (layer L R) (P ⊔ N.pCoreIn 2) ∧
                  t ∈ centralizer (layer L R : Set G) ∧
                  t ∈ centralizer (conjugateSpanBy (layer L R)
                    ((P ⊔ N.pCoreIn 2) ⊓ centralizer (zpowers c : Set G)) : Set G))) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,ham⟩ :=
    d.exists_ambient_amalgam_or_five_separated_core h hnat hE hs hNS hab
  let := hZ
  let := hX
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,?_⟩
  apply ham.imp_right
  rintro ⟨hd,hno,hfixed,hspan,horbit,hsep,hobs⟩
  exact ⟨hd,hno,hfixed,hspan,horbit,hsep,
    natural_five_span_retraction_data (hn ▸ h) (hn ▸ hnat) _ hcover.1 hcover.2.1 le_sup_right hab,hobs⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
