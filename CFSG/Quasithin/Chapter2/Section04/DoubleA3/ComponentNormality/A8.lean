module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6.A8Source
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.SourceCoordinates
public import Theory.GroupTheory.TwoPerfectSmallAction
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentSource
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.CentralProduct

public import Theory.SpecificGroups.SymmetricEight.FourPointComplement
public import Theory.SpecificGroups.AlternatingSix.PairedCubicResidual

/-!
# The A8 overcomponent contradiction in the original paired cubic source

The two original outer actors realize every automorphism of the normal A6
component. We use that action to align the overcomponent's eight-point
embedding with the source six-point marking, while keeping the second
involution fixed. The first A4 then fixes four letters, including the two
letters transposed by that involution. Their supported alternating group
is the required commuting A4 and extends with the involution to S4.

The actual conjugate A6 is the prime-to-three residual of the first
involution centralizer. It absorbs this complement; S4 maximality then
forces it to centralize the first block. The resulting A4 times A6
contradicts the genuine two-local cubic-rank bound.

The final theorem retains only the preceding actual A6 component and
source34 noncentrality, together with the overcomponent alternative it
excludes. It constructs the source35 actors, the compatible marking, and
all complement, residual and rank witnesses.

Source: Aschbacher–Smith 2.4.35–36, printed pp.548–549; A.3.18.
-/

public section
open Subgroup Equiv Equiv.Perm Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3.ComponentNormality.A8
open AlternatingSix.ShadowLocal

noncomputable def sixEmbedding : A6 →* Perm (Fin 8) :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 2 ⊕ Fin 6 ≃ Fin 8)).toMonoidHom.comp
    ((sumCongrHom (Fin 2) (Fin 6)).comp
      ((1 : A6 →* Perm (Fin 2)).prod (alternatingGroup (Fin 6)).subtype))

theorem sixEmbedding_injective : Function.Injective sixEmbedding := by
  intro a b h
  have hp := (Equiv.permCongrHom finSumFinEquiv).injective h
  have hq := sumCongrHom_injective hp
  exact Subtype.ext (congrArg Prod.snd hq)

theorem sixEmbedding_six (a : A6) (i : Fin 6) :
    sixEmbedding a (Fin.natAdd 2 i) = Fin.natAdd 2 (a.val i) := by
  change (finSumFinEquiv : Fin 2 ⊕ Fin 6 ≃ Fin 8)
    (Equiv.sumCongr (1 : Perm (Fin 2)) a.val
      (finSumFinEquiv.symm (Fin.natAdd 2 i))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem sixEmbedding_two (a : A6) (i : Fin 2) :
    sixEmbedding a (Fin.castAdd 6 i) = Fin.castAdd 6 i := by
  change (finSumFinEquiv : Fin 2 ⊕ Fin 6 ≃ Fin 8)
    (Equiv.sumCongr (1 : Perm (Fin 2)) a.val
      (finSumFinEquiv.symm (Fin.castAdd 6 i))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem sixEmbedding_range : sixEmbedding.range = alternatingGroup (Fin 8) ⊓
    (MulAction.stabilizer (Perm (Fin 8)) (0 : Fin 8) ⊓
     MulAction.stabilizer (Perm (Fin 8)) (1 : Fin 8)) := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨a,rfl⟩
    refine ⟨?_,?_,?_⟩
    · change sixEmbedding a ∈ alternatingGroup (Fin 8)
      rw [mem_alternatingGroup]
      change sign ((finSumFinEquiv : Fin 2 ⊕ Fin 6 ≃ Fin 8).permCongr
        (Equiv.sumCongr 1 a.val)) = 1
      rw [sign_permCongr, sign_sumCongr, map_one, one_mul]
      exact mem_alternatingGroup.mp a.property
    · exact sixEmbedding_two a 0
    · exact sixEmbedding_two a 1
  · rw [Theory.SpecificGroups.SymmetricEight.ComponentMarking.card_evenPairFixer,
      ← Nat.card_congr (MonoidHom.ofInjective sixEmbedding_injective).toEquiv,
      card_A6]

theorem twoPerfect_fixed_swap {P : Subgroup A6} (hP : IsPPerfect 2 P)
    {a b : Fin 6} (hab : a ≠ b)
    (hfix : ∀ p ∈ P, permutationAction (swap a b) p = p) :
    ∀ p ∈ P, p.val a = a ∧ p.val b = b := by
  let s : Finset (Fin 6) := {a,b}
  have hp (p : P) (i : Fin 6) : p.val.val i ∈ s ↔ i ∈ s := by
    have hh := congrArg Subtype.val (hfix p.val p.property)
    have he : swap a b * p.val.val = p.val.val * swap a b :=
      mul_inv_eq_iff_eq_mul.mp hh
    have hc := congrArg (fun q : Perm (Fin 6) => q i) he
    change swap a b (p.val.val i) = p.val.val (swap a b i) at hc
    have hn : swap a b (p.val.val i) ≠ p.val.val i ↔ swap a b i ≠ i := by
      rw [hc, p.val.val.injective.ne_iff]
    have hs (i : Fin 6) : swap a b i ≠ i ↔ i ∈ s := by
      simp only [s, Finset.mem_insert, Finset.mem_singleton]
      by_cases hia : i = a
      · subst i
        simp [hab, hab.symm]
      · by_cases hib : i = b
        · subst i
          simp [hab, hab.symm]
        · simp [swap_apply_of_ne_of_ne hia hib, hia, hib]
    simpa only [hs] using hn
  let ρ : P →* Perm {i // i ∈ s} := {
    toFun := fun p => p.val.val.subtypePerm (hp p)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have ht : ρ = 1 := hP.hom_eq_one_of_isPGroup
    (IsPGroup.of_card (n := 1) (by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe,
        Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]
      decide)) ρ
  intro p hp
  have he := DFunLike.congr_fun ht (⟨p,hp⟩ : P)
  exact ⟨congrArg (fun q : Perm {i // i ∈ s} => (q ⟨a,by simp [s]⟩).val) he,
    congrArg (fun q : Perm {i // i ∈ s} => (q ⟨b,by simp [s]⟩).val) he⟩


variable {G : Type*} [Group G] [Finite G]

/-- Full realization of the marked component automorphisms aligns an
existing symmetric-eight embedding with any prescribed six-point marking. -/
theorem compatible_symmetric_embedding (K H : Subgroup G) (t : G)
    (eK : K ≃* A6) (ρ : H →* AutA6) (hρ : Function.Surjective ρ)
    (hact : ∀ (w : H) (k : K),
      (eK.symm (ρ w (eK k)) : G) = (w : G) * (k : G) * (w : G)⁻¹)
    (hHt : H ≤ centralizer ({t} : Set G))
    (j : Perm (Fin 8) →* G) (hj : Function.Injective j)
    (hjt : j (swap (0 : Fin 8) 1) = t)
    (hK : sixEmbedding.range.map j = K) :
    ∃ j' : Perm (Fin 8) →* G, Function.Injective j' ∧
      j' (swap (0 : Fin 8) 1) = t ∧
      ∀ a : A6, j' (sixEmbedding a) = (eK.symm a : G) := by
  let k : A6 →* K := (j.comp sixEmbedding).codRestrict K (fun a =>
    hK ▸ mem_map_of_mem j ⟨a,rfl⟩)
  have hk : Function.Bijective k := by
    apply (Nat.bijective_iff_injective_and_card _).mpr
    exact ⟨fun a b h => sixEmbedding_injective (hj (congrArg Subtype.val h)),
      (Nat.card_congr eK.toEquiv).symm⟩
  let ek : A6 ≃* K := MulEquiv.ofBijective k hk
  obtain ⟨w,hw⟩ := hρ (eK.symm.trans ek.symm)
  let j' := (MulAut.conj (w : G)).toMonoidHom.comp j
  refine ⟨j', (MulAut.conj (w : G)).injective.comp hj, ?_, ?_⟩
  · change (w : G) * j (swap 0 1) * (w : G)⁻¹ = t
    rw [hjt, mem_centralizer_singleton_iff.mp (hHt w.property), mul_inv_cancel_right]
  · intro a
    have ha := hact w (ek a)
    rw [hw] at ha
    have hek : (ek a : G) = j (sixEmbedding a) := rfl
    change (w : G) * j (sixEmbedding a) * (w : G)⁻¹ = _
    simpa only [MulEquiv.trans_apply, eK.symm_apply_apply, ek.symm_apply_apply, hek] using ha.symm

omit [Finite G] in
/-- The actual compatible A8 marking gives the unaligned embedding on
which the full component action performs the alignment. -/
theorem embedding_of_marked_extension {E K : Subgroup G} (t : G)
    (hKE : K ≤ E)
    (f : (E ⊔ zpowers t : Subgroup G) ≃* Perm (Fin 8))
    (hft : f ⟨t, mem_sup_right (mem_zpowers t)⟩ = swap 0 1)
    (hfK : (K.subgroupOf (E ⊔ zpowers t)).map f.toMonoidHom =
      alternatingGroup (Fin 8) ⊓
        (MulAction.stabilizer (Perm (Fin 8)) (0 : Fin 8) ⊓
         MulAction.stabilizer (Perm (Fin 8)) (1 : Fin 8))) :
    ∃ j : Perm (Fin 8) →* G, Function.Injective j ∧
      j (swap (0 : Fin 8) 1) = t ∧ sixEmbedding.range.map j = K := by
  let J := E ⊔ zpowers t
  let j : Perm (Fin 8) →* G := J.subtype.comp f.symm.toMonoidHom
  refine ⟨j, J.subtype_injective.comp f.symm.injective, ?_, ?_⟩
  · change (f.symm (swap 0 1) : G) = t
    rw [← hft, f.symm_apply_apply]
  · rw [sixEmbedding_range, ← hfK]
    change ((K.subgroupOf J).map f.toMonoidHom).map
      (J.subtype.comp f.symm.toMonoidHom) = K
    have hid : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id J := by
      apply MonoidHom.ext
      intro x
      exact f.symm_apply_apply x
    rw [map_map, MonoidHom.comp_assoc, hid, MonoidHom.comp_id,
      map_subgroupOf_eq_of_le (hKE.trans le_sup_left)]


omit [Finite G] in
/-- A compatible symmetric embedding turns the source fixed transposition
on the six-point component into the four-letter alternating complement. -/
theorem complement_of_compatible_embedding (K L : Subgroup G)
    (hLK : L ≤ K) (hp : IsPPerfect 2 L) (eK : K ≃* A6)
    (σ : Perm (Fin 6)) (hσ : σ.IsSwap)
    (hfix : ∀ l ∈ (L.subgroupOf K).map eK.toMonoidHom, permutationAction σ l = l)
    (t : G) (j : Perm (Fin 8) →* G) (hj : Function.Injective j)
    (hjt : j (swap (0 : Fin 8) 1) = t)
    (hmark : ∀ a : A6, j (sixEmbedding a) = (eK.symm a : G)) :
    ∃ B : Subgroup G, B ≤ centralizer (L : Set G) ∧
      Nonempty (B ≃* alternatingGroup (Fin 4)) ∧
      Nonempty ((B ⊔ zpowers t : Subgroup G) ≃* Perm (Fin 4)) := by
  obtain ⟨a,b,hab,rfl⟩ := hσ
  let N := (L.subgroupOf K).map eK.toMonoidHom
  let eN : L ≃* N := (subgroupOfEquivOfLe hLK).symm.trans
    (eK.subgroupMap (L.subgroupOf K))
  have hpN : IsPPerfect 2 N := hp.of_surjective eN.toMonoidHom eN.surjective
  have hf := twoPerfect_fixed_swap hpN hab hfix
  let P : Finset (Fin 8) := {0,1,Fin.natAdd 2 a,Fin.natAdd 2 b}
  have hna0 : Fin.natAdd 2 a ≠ (0 : Fin 8) := by intro h; have := congrArg Fin.val h; simp at this
  have hna1 : Fin.natAdd 2 a ≠ (1 : Fin 8) := by intro h; have := congrArg Fin.val h; simp at this; omega
  have hnb0 : Fin.natAdd 2 b ≠ (0 : Fin 8) := by intro h; have := congrArg Fin.val h; simp at this
  have hnb1 : Fin.natAdd 2 b ≠ (1 : Fin 8) := by intro h; have := congrArg Fin.val h; simp at this; omega
  have hnab : Fin.natAdd 2 a ≠ Fin.natAdd 2 b := by
    intro h
    apply hab
    apply Fin.ext
    have := congrArg Fin.val h
    simpa only [Fin.val_natAdd] using Nat.add_left_cancel this
  have hcP : P.card = 4 := by
    simp [P,hna0.symm,hna1.symm,hnb0.symm,hnb1.symm,hnab]
  have hNP : ∀ p ∈ N.map sixEmbedding, ∀ i ∈ P, p i = i := by
    rintro _ ⟨n,hn,rfl⟩ i hi
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact sixEmbedding_two n 0
    · exact sixEmbedding_two n 1
    · rw [sixEmbedding_six, (hf n hn).1]
    · rw [sixEmbedding_six, (hf n hn).2]
  obtain ⟨B,hBA,hBC,⟨eB⟩,hnB,⟨eS⟩⟩ := Theory.SpecificGroups.SymmetricEight.FourPointComplement.exists_complement
    P hcP (by simp [P] : (0 : Fin 8) ∈ P) (by simp [P] : (1 : Fin 8) ∈ P)
    (by decide : (0 : Fin 8) ≠ 1) (N.map sixEmbedding) hNP
  let B' := B.map j
  have hB'C : B' ≤ centralizer (L : Set G) := by
    rintro _ ⟨v,hv,rfl⟩ l hl
    let k : K := ⟨l,hLK hl⟩
    have hlN : sixEmbedding (eK k) ∈ N.map sixEmbedding :=
      mem_map_of_mem _ (mem_map_of_mem eK.toMonoidHom hl)
    have he := congrArg j (hBC hv (sixEmbedding (eK k)) hlN)
    simpa only [map_mul, hmark, eK.symm_apply_apply] using he
  have heS : (B ⊔ zpowers (swap (0 : Fin 8) 1)).map j = B' ⊔ zpowers t := by
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,hjt]
  exact ⟨B',hB'C,⟨(B.equivMapOfInjective j hj).symm.trans eB⟩,
    ⟨(MulEquiv.subgroupCongr heS.symm).trans
      (((B ⊔ zpowers (swap (0 : Fin 8) 1)).equivMapOfInjective j hj).symm.trans eS)⟩⟩


/-- The two original outer actors align the A8 overcomponent with the
actual first block; no assertion about an arbitrary A4 marking is used. -/
theorem complement_of_a8_overcomponent (t : G) (ht : orderOf t = 2)
    (K : Subgroup (centralizer ({t} : Set G))) [K.Normal]
    (L : Subgroup G) (hLK : L ≤ K.map (centralizer ({t} : Set G)).subtype)
    (hp : IsPPerfect 2 L) (eK : K ≃* A6)
    (u x : centralizer ({t} : Set G)) (σ : Perm (Fin 6)) (hσ : σ.IsSwap)
    (hu : conjugationAction K eK u = permutationAction σ)
    (hx : conjugationAction K eK x ∉ natural)
    (huL : (u : G) ∈ centralizer (L : Set G))
    (E : Subgroup G) [IsQuasisimple E]
    (hKE : Theory.GroupTheory.IsComponentIn (K.map (centralizer ({t} : Set G)).subtype)
      (E ⊓ centralizer ({t} : Set G)))
    (htE : t ∈ normalizer (E : Set G))
    (eQ : (E ⧸ center E) ≃* alternatingGroup (Fin 8)) :
    ∃ B : Subgroup G, B ≤ centralizer (L : Set G) ∧
      Nonempty (B ≃* alternatingGroup (Fin 4)) ∧
      Nonempty ((B ⊔ zpowers t : Subgroup G) ≃* Perm (Fin 4)) := by
  let H := centralizer ({t} : Set G)
  let KA := K.map H.subtype
  let ek : K ≃* KA := K.equivMapOfInjective H.subtype H.subtype_injective
  let eKA : KA ≃* A6 := ek.symm.trans eK
  have hKEle : KA ≤ E := hKE.1.trans inf_le_left
  obtain ⟨eE⟩ := Section05.Overcomponents.FullA6.a8_model_of_quotient KA E hKEle eKA eQ
  have hcardK : Nat.card KA = 360 := (Nat.card_congr eKA.toEquiv).trans card_A6
  have hcardE : Nat.card E = 20160 := by
    rw [Nat.card_congr eE.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hlt : KA < E := lt_of_le_of_ne hKEle (by
    intro he
    have hh := congrArg (fun A : Subgroup G => Nat.card A) he
    rw [hcardK,hcardE] at hh
    omega)
  obtain ⟨f,hft,_,hfK⟩ := Theory.SpecificGroups.SymmetricEight.ComponentMarking.exists_marked_equiv
    eE htE ht hlt hKE hcardK
  obtain ⟨j,hj,hjt,hjK⟩ := embedding_of_marked_extension t hKEle f hft hfK
  let ρ := conjugationAction K eK
  have hρ := conjugation_surjective_of_source_outer_actions K eK u x σ hσ hu hx
  have hact (w : H) (k : KA) :
      (eKA.symm (ρ w (eKA k)) : G) = (w : G)*(k : G)*(w : G)⁻¹ := by
    change ((eK.symm (conjugationAction K eK w (eK (ek.symm k))) : H) : G) = _
    rw [conjugationAction_apply,eK.symm_apply_apply]
    change (w : G)*((ek (ek.symm k) : KA) : G)*(w : G)⁻¹ = _
    rw [ek.apply_symm_apply]
  obtain ⟨j',hj',hjt',hmark⟩ := compatible_symmetric_embedding KA H t eKA ρ hρ hact
    le_rfl j hj hjt hjK
  apply complement_of_compatible_embedding KA L hLK hp eKA σ hσ ?_ t j' hj' hjt' hmark
  rintro _ ⟨k,hk,rfl⟩
  rw [← hu]
  change ρ u (eKA k) = eKA k
  apply eKA.symm.injective
  apply Subtype.ext
  rw [hact, eKA.symm_apply_apply, ← huL k hk, mul_inv_cancel_right]


variable {M : Subgroup G} {d : MinimalBlockSetup M} {T : Sylow 2 G}
  {c : SourcePairCoordinates d T}

/-- The original paired coordinates supply exactly the two outer actors
needed for the compatible A8 embedding. This reuses source35's proved
transposition and four-group movement theorems on the literal subgroups. -/
theorem actors_of_original (g : SourceCentralizerGeometry c)
    (K : Subgroup (centralizer ({g.z₂} : Set G))) [K.Normal]
    (hLK : d.block.map d.H.subtype ≤ K.map (centralizer ({g.z₂} : Set G)).subtype)
    (eK : K ≃* A6)
    (hVK : ¬ c.U₂.subgroupOf (centralizer ({g.z₂} : Set G)) ≤
      centralizer (K : Set (centralizer ({g.z₂} : Set G)))) :
    ∃ (e : K ≃* A6) (u : centralizer ({g.z₂} : Set G)) (σ : Perm (Fin 6)),
      (u : G) ∈ c.U₂ ∧ σ.IsSwap ∧
      conjugationAction K e u = permutationAction σ ∧
      conjugationAction K e ⟨c.x,g.x_second⟩ ∉ natural := by
  let H := centralizer ({g.z₂} : Set G)
  let L := (d.block.map d.H.subtype).subgroupOf H
  let U := c.U₁.subgroupOf H
  let V := c.U₂.subgroupOf H
  have hUR : c.U₁ ≤ sourceR d := c.baumann ▸ c.first.module_le
  have hVR : c.U₂ ≤ sourceR d := c.baumann ▸ c.second.module_le
  have hRH : sourceR d ≤ H := fun r hr =>
    mem_centralizer_singleton_iff.mpr (g.second_fixed r hr)
  have hLH : d.block.map d.H.subtype ≤ H := hLK.trans (map_subtype_le _)
  have hUH : c.U₁ ≤ H := hUR.trans hRH
  have hVH : c.U₂ ≤ H := hVR.trans hRH
  have hLKi : L ≤ K := by
    intro l hl
    obtain ⟨v,hv,he⟩ := hLK hl
    exact H.subtype_injective he ▸ hv
  have hUK : U ≤ K := by
    intro u hu
    obtain ⟨v,hv,he⟩ := hLK ((map_subtype_le _) hu)
    exact H.subtype_injective he ▸ hv
  obtain ⟨eL⟩ := ChapterC.IsAlternatingBlock.equiv_alternatingFour c.cubic_first
  let eLi : L ≃* alternatingGroup (Fin 4) := (subgroupOfEquivOfLe hLH).trans eL
  let : IsElementaryAbelian 2 c.U₁ := c.first.elementary
  let : IsElementaryAbelian 2 c.U₂ := c.second.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hVH
  have hUcard : Nat.card U = 4 := (Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv).trans
    (ChapterC.Section05.BlockAnalysis.RankOneSetup.cubic_module_card c.cubic_first)
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour U := ⟨hUcard,IsElementaryAbelian.exponent_eq_prime⟩
  have hVL : V ≤ centralizer (L : Set H) := by
    intro v hv l hl
    apply Subtype.ext
    exact c.commute ((map_subtype_le _) hv) l hl
  obtain ⟨e,u,hu,σ,hσ,ha⟩ := transposition_of_two_component_models K L V hLKi eLi
    (.inl ⟨eK⟩) (fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv) hVL hVK
  let x : H := ⟨c.x,g.x_second⟩
  have hUP : U ≤ (g.P₂ : Subgroup H) := by
    intro u hu
    have hh : (u : G) ∈ (g.P₂ : Subgroup H).map H.subtype :=
      g.second_span.symm ▸ mem_sup_left (hUR hu)
    obtain ⟨v,hv,he⟩ := hh
    exact H.subtype_injective he ▸ hv
  have hxP : x ∈ (g.P₂ : Subgroup H) := by
    have hh : c.x ∈ (g.P₂ : Subgroup H).map H.subtype :=
      g.second_span.symm ▸ mem_sup_right (mem_zpowers c.x)
    obtain ⟨v,hv,he⟩ := hh
    exact (show v = x from Subtype.ext he) ▸ hv
  have hm : ¬ U.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U : Set H) := by
    intro hh
    apply c.noncommuting
    rintro _ ⟨v,hv,rfl⟩ w hw
    let vH : H := ⟨v,hUH hv⟩
    let wH : H := ⟨w,hUH hw⟩
    exact congrArg Subtype.val (hh (mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom
      (show vH ∈ U from hv)) wH hw)
  exact ⟨e,u,σ,hu,hσ,ha,conjugationAction_not_natural_of_four_movement K e
    (g.P₂ : Subgroup H) U g.P₂.isPGroup' hUK hUP x hxP hm⟩

/-- The original A8-overcomponent alternative contradicts the paired cubic
configuration. The earlier actual A6 component and source34 noncentrality
are retained; source35 and every subsequent geometric step are discharged. -/
theorem contradiction_of_original (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (g : SourceCentralizerGeometry c)
    (K : Subgroup (centralizer ({g.z₂} : Set G))) [K.Normal]
    (hK : IsComponent (centralizer ({g.z₂} : Set G)) K)
    (hLK : d.block.map d.H.subtype ≤ K.map (centralizer ({g.z₂} : Set G)).subtype)
    (eK : K ≃* A6)
    (hVK : ¬ c.U₂.subgroupOf (centralizer ({g.z₂} : Set G)) ≤
      centralizer (K : Set (centralizer ({g.z₂} : Set G))))
    (E : Subgroup G) [IsQuasisimple E]
    (hKE : IsComponentIn (K.map (centralizer ({g.z₂} : Set G)).subtype)
      (E ⊓ centralizer ({g.z₂} : Set G)))
    (htE : g.z₂ ∈ normalizer (E : Set G))
    (eQ : (E ⧸ center E) ≃* alternatingGroup (Fin 8)) : False := by
  let H := centralizer ({g.z₂} : Set G)
  let KA := K.map H.subtype
  let L := d.block.map d.H.subtype
  obtain ⟨e,u,σ,hu,hσ,hua,hxa⟩ := actors_of_original g K hLK eK hVK
  have huL : (u : G) ∈ centralizer (L : Set G) := c.commute ((map_subtype_le _) hu)
  obtain ⟨B,hBC,⟨eB⟩,⟨eS⟩⟩ := complement_of_a8_overcomponent g.z₂ g.order_second
    K L hLK c.first.short.twoPerfect e u ⟨c.x,g.x_second⟩ σ hσ hua hxa huL E hKE htE eQ
  let Ks := KA.map (MulAut.conj c.s).toMonoidHom
  have hKA : IsComponentIn KA H := by
    refine ⟨map_subtype_le _,?_⟩
    change IsComponent H ((K.map H.subtype).comap H.subtype)
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  have hHs : H.map (MulAut.conj c.s).toMonoidHom = centralizer ({g.z₁} : Set G) := by
    ext y
    rw [mem_map_equiv,mem_centralizer_singleton_iff,mem_centralizer_singleton_iff]
    change c.s⁻¹*y*c.s*g.z₂=g.z₂*(c.s⁻¹*y*c.s) ↔ y*g.z₁=g.z₁*y
    rw [←g.exchange_second]
    constructor
    · intro hh
      apply_fun (fun a : G => c.s*a*c.s⁻¹) at hh
      simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,
        mul_inv_cancel,mul_one,one_mul] using hh
    · intro hh
      apply_fun (fun a : G => c.s⁻¹*a*c.s) at hh
      simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,
        mul_inv_cancel,mul_one,one_mul] using hh
  have hKs : IsComponentIn Ks (centralizer ({g.z₁} : Set G)) := by
    simpa only [hHs] using hKA.map (MulAut.conj c.s)
  let eKA := (K.equivMapOfInjective H.subtype H.subtype_injective).symm.trans eK
  let eKs : Ks ≃* A6 := (KA.equivMapOfInjective (MulAut.conj c.s).toMonoidHom
    (MulAut.conj c.s).injective).symm.trans eKA
  have hDK : c.L ≤ Ks := by
    rw [←c.exchange]
    exact map_mono hLK
  obtain ⟨eL⟩ := ChapterC.IsAlternatingBlock.equiv_alternatingFour c.cubic_first
  obtain ⟨eD⟩ := ChapterC.IsAlternatingBlock.equiv_alternatingFour c.cubic_second
  exact AlternatingSix.PairedCubicResidual.paired_cubic_a8_false hG.quasithin
    Ks L B c.L g.z₁ g.order_first ((map_subtype_le _) g.first_mem)
    hKs.1 hKs.2 eKs eL eB eD hDK hBC c.commute g.z₂
    ((map_subtype_le _) g.second_mem) eS

end CFSG.Quasithin.Chapter2.DoubleA3.ComponentNormality.A8
