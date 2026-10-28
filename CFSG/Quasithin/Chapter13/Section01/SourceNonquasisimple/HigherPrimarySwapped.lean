module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.HigherPrimaryComponent
public import Theory.SpecificGroups.PSL3.PrimeAutomorphismExponent
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.PGroup.HomocyclicOmegaFrattini

/-!
# Eliminating the actual higher-primary linear-three branch

Let I_p/O₂(I_p) be homocyclic of rank two and exponent p^a, with a≥2.
In the escaping maximal two-local already constructed, the intrinsic
embedding theorem leaves a swapped rank-one component or a T-invariant
linear-three component. In the latter case K is normal in H. Choose a
Sylow p-subgroup S of I_p containing the actual canonical plane P.

The quotient comparison identifies S with the higher homocyclic group,
so every element of P is a p-power root image. Every p-element of
Aut(K/O₂(K)) has pth power one by the prime-field PSL₃ calculation and
faithfulness of the central-quotient action. Thus P centralizes K/O₂(K).
But P lies in K and injects modulo O₂(K), while the component center has
order prime to p. This contradiction removes the linear-three branch.

The public theorem retains the literal escaping H, its swapped component,
the canonical plane, both normalizing two-cores, and the actual rank-one
models. Block recognition in this surviving case remains a source obligation.
No activity of I_p on a module is inferred from its order-p subgroup.

Source: Aschbacher--Smith3.2.14, printed p.585;13.1.4(5), p.867;
the surviving intrinsic embeddings in1.3.4, pp.509--511.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
open Chapter1 Chapter1.Section02 Chapter1.XiEmbedding Chapter1.RadicalExclusions
open Chapter1.RadicalExclusions.ModelReduction Chapter12.Section02 ChapterA.Section04

private theorem linear_three_automorphism_prime_power_exponent
    {Q : Type*} [Group Q] [Finite Q] (hq : IsQuasisimple Q)
    {p : ℕ} [Fact p.Prime] (hp : 5 < p) (hm : LinearThreeModel p Q)
    (a : MulAut Q) {m : ℕ} (ha : a^(p^m)=1) : a^p=1 := by
  let := hq
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · let : IsQuasisimple SL(3,F) := hq.of_mulEquiv e
    let : IsSimpleGroup PSL(3,F) := IsQuasisimple.simple
    let f : MulAut Q →* MulAut PSL(3,F) :=
      (quotientAut (center SL(3,F))).comp (MulAut.congr e).toMonoidHom
    have hf : Function.Injective f := MulAut.quotient_center_injective.comp (MulAut.congr e).injective
    apply hf
    rw [map_pow,map_one]
    apply Matrix.PSL3.OddPrimeAutomorphisms.prime_power_exponent hp hF
    rw [← map_pow,ha,map_one]
  · let : IsQuasisimple PSL(3,F) := hq.of_mulEquiv e
    let : IsSimpleGroup PSL(3,F) := by
      let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect (F := F) 3 (by decide)
      let : IsSimpleGroup (PSL(3,F) ⧸ center PSL(3,F)) := IsQuasisimple.simple
      exact (((QuotientGroup.quotientMulEquivOfEq
        (Group.IsPerfect.center_quotient_center_eq_bot SL(3,F))).trans QuotientGroup.quotientBot).symm).isSimpleGroup
    let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect (F := F) 3 (by decide)
    apply (MulAut.congr e).injective
    rw [map_pow,map_one]
    apply Matrix.PSL3.OddPrimeAutomorphisms.prime_power_exponent hp hF
    rw [← map_pow,ha,map_one]

private theorem homocyclic_omega_killed_of_image_exponent
    {S A : Type*} [Group S] [Finite S] [Group A] {p a : ℕ} [Fact p.Prime]
    (ha : 2 ≤ a) (e : S ≃* Multiplicative (Fin 2 → ZMod (p^a)))
    (f : S →* A) (hf : ∀ s, f s ^ p = 1) (x : S) (hx : x^p=1) : f x=1 := by
  let : IsMulCommutative S := ⟨⟨fun s t => e.injective (by rw [map_mul,map_mul,mul_comm])⟩⟩
  have hxω : x ∈ omega S (p := p) 1 := by
    rw [OmegaAction.omega_eq_pow_ker]
    simpa only [MonoidHom.mem_ker,powMonoidHom_apply,pow_one] using hx
  let b : omega S (p := p) 1 := ⟨x,hxω⟩
  let j := HomocyclicOmegaFrattini.equiv (κ := Fin 2) (by omega : 1 ≤ a) e
  obtain ⟨y,hy⟩ := QuotientGroup.mk'_surjective (frattini S) (j.symm b)
  have hroot : y^(p^(a-1))=x := by
    have hh := congrArg j hy
    rw [j.apply_symm_apply] at hh
    exact (HomocyclicOmegaFrattini.equiv_apply_mk (by omega : 1 ≤ a) e y).symm.trans
      (congrArg Subtype.val hh)
  have he : p^(a-1)=p*p^(a-2) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [← hroot,map_pow,he,pow_mul,hf,one_pow]

private noncomputable def primarySylowQuotientEquiv
    {G : Type*} [Group G] [Finite G] {I : Subgroup G} {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hq : IsPGroup p (XiQuotient I)) (S : Sylow p I) : S ≃* XiQuotient I := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let f : S →* XiQuotient I := q.comp (S : Subgroup I).subtype
  apply MulEquiv.ofBijective f
  constructor
  · apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    have hc : (a : I) ∈ pCore 2 I := (QuotientGroup.eq_one_iff _).mp ha
    have hd : Disjoint (pCore 2 I) (S : Subgroup I) :=
      pCore_isPGroup.disjoint_of_coprime S.isPGroup' (Nat.coprime_two_left.mpr ho)
    exact Subtype.ext (hd.le_bot ⟨hc,a.property⟩)
  · apply MonoidHom.range_eq_top.mp
    have ht : (S : Subgroup I).map q=⊤ := top_unique
      ((hq.to_subgroup ⊤).le_sylow_of_normal (S.mapSurjective (QuotientGroup.mk'_surjective _)))
    simpa only [f,MonoidHom.range_comp,range_subtype] using ht

private theorem component_normal_of_T
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {H K : Subgroup G} (hH : IsTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ cComponentsIn H) (hTK : (T : Subgroup G) ≤ normalizer K) :
    (K.subgroupOf H).Normal := by
  let B := K.subgroupOf H
  let S := T.subtype hTH
  have hsq := hG.twoLocal_sqtk hH
  have hsqQ : IsSQTK KnownSimple.IsKnownSimple (XiQuotient H) :=
    ⟨quotient_stronglyQuasithin hsq.stronglyQuasithin,hsq.isKGroup.quotient _⟩
  have hindex : B.Normal ∨ (normalizer (B : Set H)).index=2 := by
    let := pCore_isNilpotent (p := 2) (G := H)
    apply cComponent_normal_or_index_two_of_quotient hK.2 (pCore 2 H)
    exact ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
      (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
      hsqQ (pCore_quotient_pCore_eq_bot 2) (hK.2.map_quotient _)
  have hn := componentOrbit_normal_of_normal_or_index_two B S hindex
  have hSB : (S : Subgroup H) ≤ normalizer (B : Set H) := by
    rw [← subgroupOf_normalizer_eq hK.1]
    exact comap_mono hTK
  have he : componentOrbit B (S : Subgroup H)=B := le_antisymm
    (iSup_conjugates_le_of_le_normalizer B S B le_rfl hSB) (le_componentOrbit B S)
  rw [he] at hn
  exact hn

private theorem higher_primary_linear_three_impossible
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G T)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hp : 5 < p)
    (hshape : XiOddQuotient p (XiQuotient (XiP p L)))
    {a : ℕ} (ha : 2 ≤ a)
    (e : XiQuotient (Chapter3.RadicalCentralization.primaryRadical p L) ≃*
      Multiplicative (Fin 2 → ZMod (p^a)))
    {H K P : Subgroup G} (hH : IsTwoLocal H)
    (hIH : Chapter3.RadicalCentralization.primaryRadical p L ⊔ (T : Subgroup G) ≤ H)
    (hK : K ∈ cComponentsIn H) (hq : IsQuasisimple (XiQuotient K))
    (hXK : XiP p L ≤ componentOrbit K T)
    (d : LocalInput p T (XiP p L) P H) (heP : Nonempty (P ≃* Plane p))
    (hTK : (T : Subgroup G) ≤ normalizer K)
    (hm : LinearThreeModel p (XiQuotient K)) : False := by
  let I := Chapter3.RadicalCentralization.primaryRadical p L
  have hXI : XiP p L ≤ I := Chapter3.RadicalCentralization.XiP_le_primaryRadical L hshape
  have hPI : P ≤ I := d.complement_le.trans hXI
  have hIQ := Chapter3.RadicalCentralization.primaryRadical_quotient_isPGroup hG T hL ho
  have hPIgroup : IsPGroup p (P.subgroupOf I) := d.odd_complement.isPGroup.comap_subtype
  obtain ⟨S,hPS⟩ := hPIgroup.exists_le_sylow
  let es := (primarySylowQuotientEquiv ho hIQ S).trans e
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hIH
  have hKN := component_normal_of_T hG hH hTH hK hTK
  have hHN : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hK.1).mp hKN
  have hIN : I ≤ normalizer (K : Set G) := le_sup_left.trans (hIH.trans hHN)
  let r : S →* normalizer (K : Set G) := {
    toFun s := ⟨((s : I) : G),hIN (s : I).property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let f : S →* MulAut (XiQuotient K) :=
    (quotientAut (pCore 2 K)).comp (K.normalizerMonoidHom.comp r)
  have hf (s : S) : f s ^ p=1 := by
    obtain ⟨m,hs⟩ := S.isPGroup' s
    apply linear_three_automorphism_prime_power_exponent hq hp hm
    rw [← map_pow,hs,map_one]
  have hPK : P ≤ K := d.complement_le.trans
    (hXK.trans (iSup_conjugates_le_of_le_normalizer K T K le_rfl hTK))
  let eP := heP.some
  have hPexp (x : P) : x^p=1 := by
    apply eP.injective
    rw [map_pow,map_one]
    apply Multiplicative.toAdd.injective
    funext i
    change p • (eP x).toAdd i=0
    rw [nsmul_eq_mul]
    simp
  have hPne : P ≠ ⊥ := by
    intro hz
    have hc : Nat.card P=p^2 := (Nat.card_congr eP.toEquiv).trans (plane_card p)
    rw [hz,Subgroup.card_bot] at hc
    nlinarith
  let : Nontrivial P := (nontrivial_iff_ne_bot P).mpr hPne
  obtain ⟨x,hx,hx1⟩ := P.exists_ne_one_of_nontrivial
  let sx : S := ⟨⟨x,hPI hx⟩,hPS hx⟩
  have hxpG : x^p=1 := congrArg (fun y : P => (y : G)) (hPexp ⟨x,hx⟩)
  have hsxp : sx^p=1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hxpG
  have hfx : f sx=1 := homocyclic_omega_killed_of_image_exponent ha es f hf sx hsxp
  let q := QuotientGroup.mk' (pCore 2 K)
  let xK : K := ⟨x,hPK hx⟩
  have hc : q xK ∈ center (XiQuotient K) := by
    apply mem_center_iff.mpr
    intro z
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) z
    have hfix := DFunLike.congr_fun hfx (q k)
    change quotientAut (pCore 2 K) (K.normalizerMonoidHom (r sx)) (q k)=q k at hfix
    rw [quotientAut_apply_mk] at hfix
    change q (xK*k*xK⁻¹)=q k at hfix
    rw [map_mul,map_inv,map_mul] at hfix
    exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hcenter : ¬ p ∣ Nat.card (center (XiQuotient K)) := by
    rcases hm with ⟨F,_,_,_,⟨eK⟩⟩ | ⟨F,_,_,_,⟨eK⟩⟩
    · rw [Nat.card_congr (centerCongr eK).toEquiv]
      intro hd
      have := Nat.le_of_dvd (by decide : 0 < 3) (hd.trans (Matrix.SL3.card_center_dvd_three F))
      omega
    · rw [Nat.card_congr (centerCongr eK).toEquiv]
      let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect (F := F) 3 (by decide)
      rw [Group.IsPerfect.center_quotient_center_eq_bot SL(3,F),Subgroup.card_bot]
      exact (Fact.out : p.Prime).not_dvd_one
  let z : center (XiQuotient K) := ⟨q xK,hc⟩
  have hxKp : xK^p=1 := by
    apply Subtype.ext
    exact hxpG
  have hzp : z^p=1 := Subtype.ext (by change q xK^p=1; rw [← map_pow,hxKp,map_one])
  have hz : z=1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hcenter)
    (orderOf_dvd_of_pow_eq_one hzp) (orderOf_dvd_natCard z))
  have hxcore : xK ∈ pCore 2 K := (QuotientGroup.eq_one_iff xK).mp (congrArg Subtype.val hz)
  have hxcoreG : x ∈ K.pCoreIn 2 := mem_map_of_mem K.subtype hxcore
  exact hx1 ((d.odd_complement.isPGroup.disjoint_of_coprime (isPGroup_pCoreIn 2 K)
    (Nat.coprime_two_right.mpr ho)).le_bot ⟨hx,hxcoreG⟩)

/-- The actual higher-primary obstruction has only the swapped rank-one
alternative: its pth roots exclude a T-invariant linear-three component. -/
theorem active_higher_primary_escaping_swapped
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G T)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 5 < p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hi : intrinsicSignalizerModule (Chapter3.RadicalCentralization.primaryRadical p L) ≠ ⊥)
    {a : ℕ} (ha : 2 ≤ a)
    (e : Nonempty ((Chapter3.RadicalCentralization.primaryRadical p L ⧸
      pCore 2 (Chapter3.RadicalCentralization.primaryRadical p L)) ≃*
      Multiplicative (Fin 2 → ZMod (p^a))))
    (P : Sylow p (XiP p L)) :
    let I := Chapter3.RadicalCentralization.primaryRadical p L
    let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
    ∃ H K : Subgroup G, IsMaximalTwoLocal H ∧ I ⊔ (T : Subgroup G) ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧ K ∈ cComponentsIn H ∧
      K ∈ Chapter1.L G T ∧ IsQuasisimple (XiQuotient K) ∧
      XiP p L ≤ componentOrbit K T ∧ LocalInput p T (XiP p L) P₀ H ∧
      Nonempty (P₀ ≃* Plane p) ∧ SwappedFactors T P₀ K ∧ SwappedModel p (XiQuotient K) ∧
      ¬ K ≤ normalizer (L : Set G) ∧ generalizedFitting K = pCore 2 K ∧
      (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (K : Set G) ∧
      (I ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (K : Set G) := by
  obtain ⟨H,K,hH,hIH,hout,hK,hKL,hq,hXK,d,hs,hKout,hF,hR,hRI⟩ :=
    active_large_primary_escaping_component h hmany hL hn ho hp hd hi P
  rcases hs.2 with ⟨hswap,hm⟩ | ⟨hTK,hm⟩
  · exact ⟨H,K,hH,hIH,hout,hK,hKL,hq,hXK,d,hs.1,hswap,hm,hKout,hF,hR,hRI⟩
  · exact (higher_primary_linear_three_impossible h.simpleQTKE hL.1 ho hp
      (RadicalConjugateRigidity.maximal_radical_structure h.simpleQTKE T hL hn ho hd).1
      ha e.some hH.1 hIH hK hq hXK d hs.1 hTK hm).elim

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
