module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanFrattiniPairing
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSynchronizedSections
public import Theory.Representation.PSL3Two.NaturalDualCentralizer
public import Theory.GroupTheory.DisjointCommutingProjection

/-!
# The original fixed span is the unique invariant complement

The exact product Phi(Q)=UV retains the natural eight V and the actual
fixed span U. The synchronized original actor marks V as natural and
Phi(Q)/Z(Q) as dual natural. An L-invariant complement to V contains the
L-fixed four H. Its projection to V along U therefore factors through
the literal dual-natural quotient. The same-actor no-hom theorem makes
that projection zero, proving uniqueness. Actual normalizers of L
preserve Phi, V and invariance, so they normalize this same U.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryLinearThree
open scoped Pointwise MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

private theorem no_dual_natural_factored_map
    {A B : Type*} [_root_.Group A] [_root_.Group B]
    (a : A →* BinaryLinearThree.Group) (ha : Function.Surjective a)
    (act : A →* MulAut B)
    (p : B →* Multiplicative (Module.Dual (ZMod 2) Vector))
    (hp : Function.Surjective p)
    (f : B →* Multiplicative Vector) (hk : p.ker ≤ f.ker)
    (he : ∀ (l : A) (x : B),
      (p (act l x)).toAdd = W.dual (a l) (p x).toAdd)
    (hf : ∀ (l : A) (x : B),
      (f (act l x)).toAdd = W (a l) (f x).toAdd) : f = 1 := by
  let g := p.liftOfSurjective hp ⟨f,hk⟩
  have hg (x : B) : g (p x) = f x := by
    simp [g,MonoidHom.liftOfSurjective]
  let t : W.dual.IntertwiningMap W := {
    toLinearMap := (AddMonoidHom.toMultiplicative.symm g).toZModLinearMap 2
    isIntertwining' := by
      intro k
      obtain ⟨l,rfl⟩ := ha k
      apply LinearMap.ext
      intro v
      obtain ⟨x,hx⟩ := hp (Multiplicative.ofAdd v)
      have hpx : (p x).toAdd = v := congrArg Multiplicative.toAdd hx
      change (g (Multiplicative.ofAdd (W.dual (a l) v))).toAdd =
        W (a l) (g (Multiplicative.ofAdd v)).toAdd
      rw [←hpx,←he l x]
      change (g (p (act l x))).toAdd = W (a l) (g (p x)).toAdd
      rw [hg,hg,hf] }
  have ht := NaturalDual.dual_natural_zero t
  apply MonoidHom.ext
  intro x
  apply Multiplicative.toAdd.injective
  have hx := congrArg (fun s : W.dual.IntertwiningMap W => s (p x).toAdd) ht
  change (g (p x)).toAdd = 0 at hx
  rwa [hg] at hx

private theorem projection_conjugation
    {G : Type*} [Group G] (L S V U : Subgroup G)
    (hS : S = V ⊔ U) (hc : V ≤ centralizer (U : Set G))
    (hLV : L ≤ normalizer V) (hLU : L ≤ normalizer U)
    (f : S →* V) (hk : f.ker = U.subgroupOf S)
    (hf : ∀ x : S, (x : G) ∈ V → (f x : G) = (x : G))
    (l : L) (x y : S) (hy : (y : G) = l * (x : G) * (l : G)⁻¹) :
    (f y : G) = l * (f x : G) * (l : G)⁻¹ := by
  have hVS : V ≤ S := le_sup_left.trans hS.ge
  have hUS : U ≤ S := le_sup_right.trans hS.ge
  have hx : (x : G) ∈ (V : Set G) * (U : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left V U
      ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)),←hS]
    exact x.property
  obtain ⟨v,hv,u,hu,hvu⟩ := hx
  let v₀ : S := ⟨v,hVS hv⟩
  let u₀ : S := ⟨u,hUS hu⟩
  have hx' : x = v₀ * u₀ := Subtype.ext hvu.symm
  have hv' : (l : G) * v * (l : G)⁻¹ ∈ V :=
    (mem_normalizer_iff.mp (hLV l.property) v).mp hv
  have hu' : (l : G) * u * (l : G)⁻¹ ∈ U :=
    (mem_normalizer_iff.mp (hLU l.property) u).mp hu
  let v₁ : S := ⟨(l : G) * v * (l : G)⁻¹,hVS hv'⟩
  let u₁ : S := ⟨(l : G) * u * (l : G)⁻¹,hUS hu'⟩
  have hy' : y = v₁ * u₁ := by
    apply Subtype.ext
    change (y : G) = ((l : G) * v * (l : G)⁻¹) * ((l : G) * u * (l : G)⁻¹)
    rw [hy,←hvu]
    simp only [mul_assoc,inv_mul_cancel_left]
  have hfu₀ : f u₀ = 1 := MonoidHom.mem_ker.mp (hk ▸ hu)
  have hfu₁ : f u₁ = 1 := MonoidHom.mem_ker.mp (hk ▸ hu')
  rw [hy',hx',map_mul,map_mul,hfu₀,hfu₁,mul_one,mul_one,hf v₀ hv,hf v₁ hv']


private theorem fixed_seed_le_complement
    {G : Type*} [_root_.Group G]
    (L Phi H V A : Subgroup G)
    (hHP : H ≤ Phi) (hHfix : H ≤ centralizer (L : Set G))
    (hVfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hspan : Phi = A ⊔ V) (hAV : Disjoint A V)
    (hc : V ≤ centralizer (A : Set G))
    (hLV : L ≤ normalizer V) (hLA : L ≤ normalizer A) : H ≤ A := by
  obtain ⟨f,_,hk,hf⟩ := exists_projection_of_disjoint_commuting_product
    Phi V A (hspan.trans (sup_comm _ _)) hAV.symm hc
  intro h hh
  let x : Phi := ⟨h,hHP hh⟩
  have hfc : (f x : G) ∈ centralizer (L : Set G) := by
    intro l hl
    have he : (l : G) * h * l⁻¹ = h := by
      rw [hHfix hh l hl,mul_inv_cancel_right]
    have hp := projection_conjugation L Phi V A (hspan.trans (sup_comm _ _)) hc hLV hLA
      f hk hf ⟨l,hl⟩ x x he.symm
    exact mul_inv_eq_iff_eq_mul.mp hp.symm
  have hf1 : f x = 1 := Subtype.ext (hVfix.le ⟨(f x).property,hfc⟩)
  have hx := MonoidHom.mem_ker.mpr hf1
  rw [hk] at hx
  exact hx

private theorem unique_marked_complement
    {G : Type*} [_root_.Group G]
    (L Phi ZQ H V U A : Subgroup G)
    (a : L →* BinaryLinearThree.Group) (ha : Function.Surjective a)
    (hV : HasSectionModel L V ⊥ a W)
    (hPhi : HasSectionModel L Phi ZQ a W.dual)
    (hZ : ZQ = H ⊔ V) (hHU : H ≤ U) (hHA : H ≤ A)
    (hspanU : Phi = U ⊔ V) (hspanA : Phi = A ⊔ V)
    (hUV : Disjoint U V) (hAV : Disjoint A V)
    (hPV : Phi ≤ centralizer (V : Set G))
    (hLU : L ≤ normalizer U) (hLA : L ≤ normalizer A) : A = U := by
  have hUP : U ≤ Phi := le_sup_left.trans hspanU.ge
  have hAP : A ≤ Phi := le_sup_left.trans hspanA.ge
  have hVP : V ≤ Phi := le_sup_right.trans hspanU.ge
  have hHP : H ≤ Phi := hHU.trans hUP
  have hVU : V ≤ centralizer (U : Set G) := le_centralizer_iff.mp (hUP.trans hPV)
  have hVA : V ≤ centralizer (A : Set G) := le_centralizer_iff.mp (hAP.trans hPV)
  have hHZ : H ≤ ZQ := le_sup_left.trans hZ.ge
  have hVZ : V ≤ ZQ := le_sup_right.trans hZ.ge
  have hAZ : A ⊓ ZQ ≤ H := by
    rintro x ⟨hxA,hxZ⟩
    have hx : x ∈ (H : Set G) * (V : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left H V
        ((hVU.trans (centralizer_le hHU)).trans (Subgroup.centralizer_le_normalizer _)),←hZ]
      exact hxZ
    obtain ⟨h,hh,v,hv,hx⟩ := hx
    change h * v = x at hx
    have hvA : v ∈ A := by
      have hm := A.mul_mem (A.inv_mem (hHA hh)) hxA
      rw [←hx] at hm
      simpa only [inv_mul_cancel_left] using hm
    have hv1 : v = 1 := (hAV.eq_bot.le ⟨hvA,hv⟩ : v ∈ (⊥ : Subgroup G))
    rw [←hx,hv1,mul_one]
    exact hh
  obtain ⟨hZP,hLP,_,hn,e,he⟩ := hPhi
  let := hn
  let p : Phi →* Multiplicative (Module.Dual (ZMod 2) Vector) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (ZQ.subgroupOf Phi))
  have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hpk : p.ker = ZQ.subgroupOf Phi := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hpV (v : Phi) (hv : (v : G) ∈ V) : p v = 1 :=
    MonoidHom.mem_ker.mp (hpk ▸ hVZ hv)
  let pA : A →* Multiplicative (Module.Dual (ZMod 2) Vector) := p.comp (inclusion hAP)
  have hpA : Function.Surjective pA := by
    intro w
    obtain ⟨x,hx⟩ := hp w
    have hxprod : (x : G) ∈ (A : Set G) * (V : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left A V
        (hVA.trans (Subgroup.centralizer_le_normalizer _)),←hspanA]
      exact x.property
    obtain ⟨y,hy,v,hv,hyv⟩ := hxprod
    let y₀ : Phi := ⟨y,hAP hy⟩
    let v₀ : Phi := ⟨v,hVP hv⟩
    have hx' : x = y₀ * v₀ := Subtype.ext hyv.symm
    refine ⟨⟨y,hy⟩,?_⟩
    change p y₀ = w
    rw [hx',map_mul,hpV v₀ hv,mul_one] at hx
    exact hx
  obtain ⟨f,_,hfk,hfid⟩ := exists_projection_of_disjoint_commuting_product
    Phi V U (hspanU.trans (sup_comm _ _)) hUV.symm hVU
  obtain ⟨_,hLV,_,hnV,eV,heV⟩ := hV
  let := hnV
  let vcoords : V →* Multiplicative Vector :=
    eV.toMonoidHom.comp (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf V))
  have hvcoords : Function.Injective vcoords := (MonoidHom.ker_eq_bot_iff _).mp (by
    rw [MonoidHom.ker_comp_of_injective _ _ eV.injective,QuotientGroup.ker_mk',bot_subgroupOf])
  let fA : A →* Multiplicative Vector := vcoords.comp (f.comp (inclusion hAP))
  have hk : pA.ker ≤ fA.ker := by
    intro x hx
    have hxZ : (x : G) ∈ ZQ := by
      have hx' : inclusion hAP x ∈ p.ker := hx
      rw [hpk] at hx'
      exact hx'
    have hxH : (x : G) ∈ H := hAZ ⟨x.property,hxZ⟩
    have hfx : f (inclusion hAP x) = 1 :=
      MonoidHom.mem_ker.mp (hfk ▸ hHU hxH)
    change vcoords (f (inclusion hAP x)) = 1
    rw [hfx,map_one]
  let act : L →* MulAut A := A.normalizerMonoidHom.comp (inclusion hLA)
  have hpact (l : L) (x : A) :
      (pA (act l x)).toAdd = W.dual (a l) (pA x).toAdd :=
    he l (inclusion hAP x) (inclusion hAP (act l x)) rfl
  have hfact (l : L) (x : A) :
      (fA (act l x)).toAdd = W (a l) (fA x).toAdd := by
    apply heV l (f (inclusion hAP x)) (f (inclusion hAP (act l x)))
    exact projection_conjugation L Phi V U (hspanU.trans (sup_comm _ _)) hVU hLV hLU
      f hfk hfid l (inclusion hAP x) (inclusion hAP (act l x)) rfl
  have hfA : fA = 1 := no_dual_natural_factored_map a ha act pA hpA fA hk hpact hfact
  have hAU : A ≤ U := by
    intro x hx
    have hzero := DFunLike.congr_fun hfA (⟨x,hx⟩ : A)
    have hfx : f (inclusion hAP ⟨x,hx⟩) = 1 :=
      hvcoords (hzero.trans (map_one vcoords).symm)
    have hxk := MonoidHom.mem_ker.mpr hfx
    rw [hfk] at hxk
    exact hxk
  apply le_antisymm hAU
  intro u hu
  have huprod : u ∈ (A : Set G) * (V : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left A V
      (hVA.trans (Subgroup.centralizer_le_normalizer _)),←hspanA]
    exact hUP hu
  obtain ⟨x,hx,v,hv,hxv⟩ := huprod
  change x * v = u at hxv
  have hvU : v ∈ U := by
    have hm := U.mul_mem (U.inv_mem (hAU hx)) hu
    rw [←hxv] at hm
    simpa only [inv_mul_cancel_left] using hm
  have hv1 : v = 1 := (hUV.eq_bot.le ⟨hvU,hv⟩ : v ∈ (⊥ : Subgroup G))
  rw [←hxv,hv1,mul_one]
  exact hx

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
variable {G : Type*} [_root_.Group G] [Finite G]

/-- The literal original U is the unique L-invariant complement to V in Phi,
and every ambient normalizer of L normalizes U. -/
theorem binary_three_source_fixed_span_unique
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hzH : z ∈ LinearThree.OriginalSource.intrinsicFour c.L)
    (hz2 : orderOf z = 2) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G)))
    (hK : K.IsCComponent) (hKn : K.Normal)
    (hLK : c.L.subgroupOf (centralizer ({z} : Set G)) ≤ K)
    [IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))]
    (eB : (((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) ⧸
      pCore 2 ((c.L.subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) ≃* PSL(3,ZMod 2))
    (hrX : primeRank 3 (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))) = 2)
    (hrB : primeRank 3 (normalizer ((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))) ≤ 1)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) 4 2) :
    let C := centralizer ({z} : Set G)
    let Q := LinearThree.commutatorCore c.L
    let Phi := frattiniIn Q
    let V := ⁅coreCenter c.L,c.L⁆
    let U := conjugateSpanBy (intrinsicFour c.L) C
    (∀ A : Subgroup G, c.L ≤ normalizer A → Disjoint A V → Phi = A ⊔ V → A = U) ∧
      normalizer (c.L : Set G) ≤ normalizer U := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let ZQ := coreCenter c.L
  let H := intrinsicFour c.L
  let V := ⁅ZQ,c.L⁆
  let U := conjugateSpanBy H C
  let W₀ := conjugateSpanBy V C
  let := hKn
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  have hBK := map_mono (f := q) hLK
  have hpair := binary_three_source_fixed_span_frattini_pairing
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  have hprod : Phi = U ⊔ V := hpair.1
  have hUV : Disjoint U V := hpair.2.1
  have hUP : U ≤ Phi := le_sup_left.trans hprod.ge
  have hVP : V ≤ Phi := le_sup_right.trans hprod.ge
  have hHU : H ≤ U := le_conjugateSpanBy _ _
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  obtain ⟨_,hHcard,hHF⟩ := intrinsicFour_properties_of_MS93 d c.L b t common earlier
  have hHfix : H ≤ centralizer (c.L : Set G) := hHF.trans inf_le_right
  have hHZ : H ≤ ZQ := by
    intro x hx
    refine ⟨⟨x,(hHF hx).1⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext ((hHF hx).2 y
      (((LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)) y.property))
  have hLZ : c.L ≤ normalizer ZQ :=
    (normalizer_commutator_ge_right _ _).trans
      (normalizer_le_normalizer_characteristic_image Q (center Q))
  have hVZ : V ≤ ZQ := le_normalizer_iff_commutator_le_left.mp hLZ
  have hZcQ : ZQ ≤ centralizer (Q : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  have hPV : Phi ≤ centralizer (V : Set G) :=
    le_centralizer_iff.mp ((hVZ.trans hZcQ).trans (centralizer_le (map_subtype_le _)))
  have hVH : V ≤ normalizer H :=
    ((hVZ.trans hZcQ).trans (centralizer_le (hHF.trans inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hVcard : Nat.card V = 8 := (binary_three_source_point_central_eight
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP).2.1
  have hZcard : Nat.card ZQ = 32 := by
    change Nat.card ((center Q).map Q.subtype) = 32
    rw [card_map_of_injective Q.subtype_injective]
    exact (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.1
  have hZprod : ZQ = H ⊔ V := (eq_of_le_of_card_ge (sup_le hHZ hVZ) (by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint H V hVH (hUV.mono hHU le_rfl),
      hHcard,hVcard,hZcard])).symm
  have hWfix : W₀ ⊓ centralizer (c.L : Set G) = ⊥ := (binary_three_source_four_fixed_intersection
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP (K.map q) hBK hm).1
  have hVfix : V ⊓ centralizer (c.L : Set G) = ⊥ := bot_unique
    ((inf_le_inf_right _ (le_conjugateSpanBy V C)).trans hWfix.le)
  obtain ⟨a,ha,_,hVmodel,hPhimodel,_,_⟩ := binary_three_source_synchronized_sections
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  have hLU : c.L ≤ normalizer U := (le_sup_left.trans hLS).trans
    (le_normalizer_conjugateSpanBy _ _)
  have hLV : c.L ≤ normalizer V := hVmodel.2.1
  have hunique (A : Subgroup G) (hLA : c.L ≤ normalizer A)
      (hAV : Disjoint A V) (hspanA : Phi = A ⊔ V) : A = U := by
    have hAP : A ≤ Phi := le_sup_left.trans hspanA.ge
    have hHA : H ≤ A := fixed_seed_le_complement c.L Phi H V A (hHU.trans hUP) hHfix
      hVfix hspanA hAV (le_centralizer_iff.mp (hAP.trans hPV)) hLV hLA
    exact unique_marked_complement c.L Phi ZQ H V U A a ha hVmodel hPhimodel
      hZprod hHU hHA hprod hspanA hUV hAV hPV hLU hLA
  refine ⟨hunique,?_⟩
  intro g hg
  let f := (MulAut.conj g).toMonoidHom
  let A := U.map f
  have hmapL : c.L.map f = c.L := mem_normalizer_iff_map_conj_eq.mp hg
  have hgQ : g ∈ normalizer Q := normalizer_le_normalizer_commutatorCore c.L hg
  have hmapP : Phi.map f = Phi := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_normalizer_characteristic_image Q (frattini Q) hgQ)
  have hmapZ : ZQ.map f = ZQ := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_normalizer_characteristic_image Q (center Q) hgQ)
  have hmapV : V.map f = V := by
    change (⁅ZQ,c.L⁆ : Subgroup G).map f = ⁅ZQ,c.L⁆
    rw [map_commutator,hmapZ,hmapL]
  have hLA : c.L ≤ normalizer A := by
    have hh := (map_mono (f := f) hLU).trans (U.le_normalizer_map f)
    rwa [hmapL] at hh
  have hAV : Disjoint A V := by
    have hh := disjoint_map (f := f) (MulAut.conj g).injective hUV
    rwa [hmapV] at hh
  have hspanA : Phi = A ⊔ V := by
    have hh := congrArg (fun B : Subgroup G => B.map f) hprod
    rwa [Subgroup.map_sup,hmapP,hmapV] at hh
  exact mem_normalizer_iff_map_conj_eq.mpr (hunique A hLA hAV hspanA)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
