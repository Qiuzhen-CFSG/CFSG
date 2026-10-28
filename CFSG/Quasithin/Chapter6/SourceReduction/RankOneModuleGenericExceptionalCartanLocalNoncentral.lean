module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNoncentralSection
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalHeld

/-!
# The original nonquasisimple Cartan rows enter a smaller SL₂ residual

For each of the two A.3.6 nonquasisimple alternatives, use the literal
image of the same containing component in Y/O₂(Y). Its Fitting quotient
is SL₂(p), p > 3, and its kernel is the odd core. The original residual
retains its quasisimple two-core quotient under these exact maps.

The cyclic actor and full Sylow therefore fix the same involution as
the original residual. Its centralizer has a proper perfect residual
identified with SL₂(p) by the restricted Fitting quotient map. The actor
and Sylow normalize this actual smaller subgroup. The source reduction
constructs this configuration in both rows without adding a premise,
while retaining the whole original W and every binary-triality clause.

The companion NoncentralExclusion module applies the prime-field exclusion
to the lifted smaller residual. Binary-triality ambient exclusion remains
an obligation of the full local escape theorem.
Source: Aschbacher–Smith A.3.6 and 5.1.13, printed pp.43–45,636,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The actual smaller involution-centralizer residual in the original
containing image. The isomorphism is the restriction of its Fitting quotient map. -/
@[expose] def NoncentralCartanSection (T : Sylow 2 G) (H A Y : Subgroup G)
    (C : Subgroup Y) : Prop :=
  let q := QuotientGroup.mk' (pCore 2 Y)
  let I := C.map q
  let R := ((residual H).subgroupOf Y).map q
  let D := (A.subgroupOf Y).map q
  let P := ((T : Subgroup G).subgroupOf Y).map q
  ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ f : I →* SL(2,ZMod p),
    Function.Surjective f ∧ f.ker = fittingSubgroup I ∧
    ∃ z : I, orderOf z = 2 ∧ f z = -1 ∧
      (z : Y ⧸ pCore 2 Y) ∈ R ∧ (z : Y ⧸ pCore 2 Y) ∈ P ∧
      R ⊔ (D ⊔ P) ≤ centralizer ({(z : Y ⧸ pCore 2 Y)} : Set (Y ⧸ pCore 2 Y)) ∧
      let J := centralizer ({z} : Set I)
      let K := (solvableResidual J).map J.subtype
      R ≤ K.map I.subtype ∧ K.map I.subtype < I ∧
      D ⊔ P ≤ normalizer (K.map I.subtype : Set (Y ⧸ pCore 2 Y)) ∧
      ∃ e : K ≃* SL(2,ZMod p), ∀ x : K, e x = f x

namespace LocalSieve
/-- Both nonquasisimple rows produce the source's smaller, quasisimple
involution-centralizer residual with the original maps and Sylow subgroup. -/
theorem noncentral_cartan_section
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (hqs : IsQuasisimple (residual H ⧸ pCore 2 (residual H)))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hRC : residual H ≤ C.map Y.subtype)
    (hm : let I := C.map (QuotientGroup.mk' (pCore 2 Y))
      A36Common I ∧ (A36Natural I ∨ A36Nilpotent I)) :
    NoncentralCartanSection T H A Y C := by
  let q := QuotientGroup.mk' (pCore 2 Y)
  let I := C.map q
  let R := ((residual H).subgroupOf Y).map q
  let D := (A.subgroupOf Y).map q
  have hTY := hH.1.1.2.trans hY.2
  let P := (T.subtype hTY).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hRC' : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  let : I.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  have hI : I.IsCComponent := hC.map_quotient (pCore 2 Y)
  have hIzero : pCore 2 I = ⊥ := by
    let e := cComponentTwoCoreQuotientEquiv hC
    rw [←pCore_map_iso 2 e,pCore_quotient_pCore_eq_bot 2,Subgroup.map_bot]
  let a := (subgroupOfEquivOfLe hRY).symm
  let r := q.subgroupMap ((residual H).subgroupOf Y)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eR := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    (r.pCoreQuotientEquiv (q.subgroupMap_surjective _) hr)
  let := hqs
  let : IsQuasisimple (R ⧸ pCore 2 R) := IsQuasisimple.of_mulEquiv eR
  let : Group.IsPerfect (residual H) := Chapter1.mem_L_isPerfect hR
  let : Group.IsPerfect ((residual H).subgroupOf Y) :=
    Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective _)
  have hPR : (P : Subgroup (Y ⧸ pCore 2 Y)) ≤ normalizer (R : Set (Y ⧸ pCore 2 Y)) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRY]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_residual H))
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  let : IsCyclic (A.subgroupOf Y) := isCyclic_of_injective (Y.subtype.subgroupComap A) (by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : G)) he)))
  let : IsCyclic D := isCyclic_of_surjective
    (q.subgroupMap (A.subgroupOf Y)) (q.subgroupMap_surjective _)
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have hoD : Odd (Nat.card D) := by
    apply Odd.of_dvd_nat _ (card_map_dvd _ q)
    rw [←inf_subgroupOf_right A Y,Nat.card_congr
      (subgroupOfEquivOfLe (show A ⊓ Y ≤ Y from inf_le_right)).toEquiv]
    exact hoA.of_dvd_nat (card_dvd_of_le (show A ⊓ Y ≤ A from inf_le_left))
  obtain ⟨p,hp,hp3,F,_,_,hF,⟨eF⟩⟩ : ∃ p : ℕ, p.Prime ∧ 3 < p ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
        Nonempty ((I ⧸ fittingSubgroup I) ≃* SL(2,F)) := by
    rcases hm.2 with hn | hn
    · obtain ⟨p,hp,hp3,F,_,_,hF,v,e,_⟩ := hn.2
      exact ⟨p,hp,hp3,F,inferInstance,inferInstance,hF,
        ⟨(QuotientGroup.quotientMulEquivOfEq hn.1.symm).trans e⟩⟩
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hn.2.2.1
      exact ⟨5,by decide,by decide,F,inferInstance,inferInstance,hF,
        ⟨(QuotientGroup.quotientMulEquivOfEq hn.1.symm).trans e⟩⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let efield : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hF,Nat.card_zmod])
  let f := (eF.trans (GorensteinWalter.sl2RingEquiv efield)).toMonoidHom.comp
    (QuotientGroup.mk' (fittingSubgroup I))
  have hf : Function.Surjective f :=
    (eF.trans (GorensteinWalter.sl2RingEquiv efield)).surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = fittingSubgroup I := by
    rw [MonoidHom.ker_comp_of_injective _ _ (eF.trans (GorensteinWalter.sl2RingEquiv efield)).injective,
      QuotientGroup.ker_mk']
  have ho : Odd (Nat.card f.ker) := by
    rw [hk,hm.1.1]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hQ : IsSQTK KnownSimple.IsKnownSimple (Y ⧸ pCore 2 Y) := by
    have hsq := Chapter3.sqtk_of_mem_H h.qtke hY.1
    refine ⟨?_,hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  exact ⟨p,hp,hp3,f,hf,hk,odd_sl2_normal_container_residual hQ (pCore_quotient_pCore_eq_bot 2)
    I R D hI (map_mono hRC') P hPR hp3 f hf hk ho hIzero hoD
    (c.image_intersection_permutes_sylow h.sylow_normalizes hTY q)
    (h.cartan_sylow_action_isSolvable c hTY q)⟩

end LocalSieve
/-- The original selected-container reduction now constructs the smaller
prime-SL₂ residual in both nonquasisimple rows. -/
theorem localCartan_escape_binary_or_noncentral_section
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    (n = 2 ∧ CartanExceptionalConclusion T L W H) ∨
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ C.Normal ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        let I := C.map (QuotientGroup.mk' (pCore 2 Y))
        A36Common I ∧ K = residual H ∧
          ((K = residual H ∧ C.Normal ∧
            Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
            ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
            n = 2 ∧ Nat.card A = 3 ∧ A ≤ C.map Y.subtype ∧
            localBorel T L ≤ omegaCentralizer T ∧
            IsOneOrTwoA5Modules L (layer L W) ∧ Nat.card B = 7 ∧
            B ≤ centralizer
              (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G)) ∨
          ((A36Natural I ∨ A36Nilpotent I) ∧ NoncentralCartanSection T H A Y C)) := by
  rcases localCartan_escape_binary_or_nonquasisimple h hH hgen c hY hescape with hout |
    ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hCn,hKC,hlt,hn,hqlt,hcommon,hKR,halt⟩
  · exact .inl hout
  · let := hCn
    refine .inr ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hCn,hKC,hlt,hn,hqlt,hcommon,hKR,?_⟩
    rcases halt with hbin | hnat | hnil
    · exact .inl hbin
    · exact .inr ⟨.inl hnat,LocalSieve.noncentral_cartan_section h hH c hY
        (hKR ▸ hKL) (hKR ▸ hqs) C hC (hKR ▸ hKC) ⟨hcommon,.inl hnat⟩⟩
    · exact .inr ⟨.inr hnil,LocalSieve.noncentral_cartan_section h hH c hY
        (hKR ▸ hKL) (hKR ▸ hqs) C hC (hKR ▸ hKC) ⟨hcommon,.inr hnil⟩⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
