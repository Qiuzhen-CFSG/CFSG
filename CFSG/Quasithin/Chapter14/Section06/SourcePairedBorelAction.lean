module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointCentralizer
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.BorelAction
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPointFlags
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines

/-!
# The actual paired Borel action in original 14.6.9

The literal point-centralizer marking lifts each alternating point stabilizer
inside I ∩ Mc. The original Sylow orbit supplies an element of T ∩ I
exchanging the two blocks. The intrinsic commutator flags transport through
this exchange, with the original action coordinates retained on both factors.
These are the action inputs for the irreducible E₀/Z₀ section in 14.6.9(k).

Source: Aschbacher--Smith, 14.6.9(k), printed p.1027.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryPermutation BinaryPermutation.AlternatingFiveFlag
open BinaryPermutation.AlternatingFiveBorel
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem pair_action_overgroup
    (I K L R : Subgroup G) (hI : I = (K ⊔ L) ⊔ R)
    (hc : L ≤ centralizer (K : Set G))
    (hR : R ≤ normalizer ((K ⊔ L : Subgroup G) : Set G))
    (hp : ∀ r ∈ R, K.conjBy r = K ∨ K.conjBy r = L)
    (g : G) (hg : g ∈ I) : K.conjBy g = K ∨ K.conjBy g = L := by
  have hKN : K ⊔ L ≤ normalizer (K : Set G) :=
    sup_le K.le_normalizer (hc.trans (Subgroup.centralizer_le_normalizer _))
  have hLN : K ⊔ L ≤ normalizer (L : Set G) :=
    sup_le ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)) L.le_normalizer
  have hg' : g ∈ ((K ⊔ L : Subgroup G) : Set G) * (R : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left (K ⊔ L) R hR, ←hI]
    exact hg
  obtain ⟨k,hk,r,hr,hkr⟩ := hg'
  change k * r = g at hkr
  rw [←hkr,conjBy_mul]
  rcases hp r hr with he | he
  · rw [he]
    exact Or.inl (mem_normalizer_iff_map_conj_eq.mp (hKN hk))
  · rw [he]
    exact Or.inr (mem_normalizer_iff_map_conj_eq.mp (hLN hk))

private theorem source_pair_action
    {I Λ K R : Subgroup G} (c : OriginalHypotheses I Λ K R R)
    (b : OrbitDecomposition (c.sylow : Subgroup I) (R.subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (g : G) (hg : g ∈ I) :
    ((b.block i).map I.subtype).conjBy g = (b.block i).map I.subtype ∨
      ((b.block i).map I.subtype).conjBy g = (b.block j).map I.subtype := by
  have hc : (b.block j).map I.subtype ≤ centralizer ((b.block i).map I.subtype : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr (b.commute hij.symm),Subgroup.map_bot]
  have hjoin := c.pair_join b i j hij hs
  exact pair_action_overgroup I _ _ R (by rw [hjoin,c.residual_sup_sylow]) hc
    (by rw [hjoin]; exact c.R_le_H.trans c.normalizes_residual)
    (c.pair_action b i j hij hs) g hg

private theorem source_pair_flag_normalized
    {I Λ K R : Subgroup G} (c : OriginalHypotheses I Λ K R R)
    (b : OrbitDecomposition (c.sylow : Subgroup I) (R.subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (Mc : Subgroup G) (F : Subgroup G → Subgroup G)
    (hF : ∀ g ∈ Mc, ∀ N : Subgroup G,
      (F N).map (MulAut.conj g).toMonoidHom = F (N.conjBy g)) :
    I ⊓ Mc ≤ normalizer ((F ((b.block i).map I.subtype) ⊔
      F ((b.block j).map I.subtype) : Subgroup G) : Set G) := by
  let W := F ((b.block i).map I.subtype) ⊔ F ((b.block j).map I.subtype)
  have hforward (g : G) (hg : g ∈ I ⊓ Mc) :
      W.map (MulAut.conj g).toMonoidHom ≤ W := by
    dsimp only [W]
    rw [Subgroup.map_sup,hF g hg.2,hF g hg.2]
    apply sup_le
    · rcases source_pair_action c b i j hij hs g hg.1 with he | he
      · rw [he]; exact le_sup_left
      · rw [he]; exact le_sup_right
    · rcases source_pair_action c b j i hij.symm hs g hg.1 with he | he
      · rw [he]; exact le_sup_right
      · rw [he]; exact le_sup_left
  intro g hg
  apply mem_normalizer_iff.mpr
  intro w
  constructor
  · intro hw
    exact hforward g hg (mem_map_of_mem _ hw)
  · intro hw
    have hh := hforward g⁻¹ ((I ⊓ Mc).inv_mem hg) (mem_map_of_mem _ hw)
    change g⁻¹ * (g * w * g⁻¹) * (g⁻¹)⁻¹ ∈ W at hh
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left,
      mul_inv_cancel_right, inv_mul_cancel, mul_one] using hh

/-- The intrinsic paired moved spaces are normalized by the literal point centralizer. -/
theorem source_paired_commutator_normalized {I Λ K R : Subgroup G} (c : OriginalHypotheses I Λ K R R)
    (b : OrbitDecomposition (c.sylow : Subgroup I) (R.subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2) (Mc : Subgroup G) :
    I ⊓ Mc ≤ normalizer ((⁅(b.block i).map I.subtype ⊓ Mc,sourceModule ((b.block i).map I.subtype)⁆ ⊔
      ⁅(b.block j).map I.subtype ⊓ Mc,sourceModule ((b.block j).map I.subtype)⁆ : Subgroup G) : Set G) := by
  apply source_pair_flag_normalized c b i j hij hs Mc
    (fun N => ⁅N ⊓ Mc,sourceModule N⁆)
  intro g hg N
  have hm : Mc.map (MulAut.conj g).toMonoidHom = Mc :=
    mem_normalizer_iff_map_conj_eq.mp (Mc.le_normalizer hg)
  rw [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    hm, sourceModule_map_equiv]
  rfl

/-- The centers of the two residual cores form an invariant plane under Iz. -/
theorem source_paired_center_normalized {I Λ K R : Subgroup G} (c : OriginalHypotheses I Λ K R R)
    (b : OrbitDecomposition (c.sylow : Subgroup I) (R.subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2) (Mc : Subgroup G) :
    let X₁ := (pResidual 2 ((b.block i).map I.subtype ⊓ Mc : Subgroup G)).map
      ((b.block i).map I.subtype ⊓ Mc).subtype
    let X₂ := (pResidual 2 ((b.block j).map I.subtype ⊓ Mc : Subgroup G)).map
      ((b.block j).map I.subtype ⊓ Mc).subtype
    I ⊓ Mc ≤ normalizer (((center (X₁.pCoreIn 2)).map (X₁.pCoreIn 2).subtype ⊔
      (center (X₂.pCoreIn 2)).map (X₂.pCoreIn 2).subtype : Subgroup G) : Set G) := by
  apply source_pair_flag_normalized c b i j hij hs Mc
    (fun N => (center (((pResidual 2 (N ⊓ Mc : Subgroup G)).map (N ⊓ Mc).subtype).pCoreIn 2)).map
      (((pResidual 2 (N ⊓ Mc : Subgroup G)).map (N ⊓ Mc).subtype).pCoreIn 2).subtype)
  intro g hg N
  have hm : Mc.map (MulAut.conj g).toMonoidHom = Mc :=
    mem_normalizer_iff_map_conj_eq.mp (Mc.le_normalizer hg)
  rw [map_map,←map_center_image_of_injective _ _ (MulAut.conj g).injective,
    map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,map_embedded_pResidual,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    hm]
  rfl

/-- Each original alternating block has its entire two-core equal to the
marked source module. -/
theorem source_paired_cores_eq_modules
    {I Λ K R : Subgroup G} (c : OriginalHypotheses I Λ K R R)
    (b : OrbitDecomposition (c.sylow : Subgroup I) (R.subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    ((b.block i).map I.subtype).pCoreIn 2 = sourceModule ((b.block i).map I.subtype) ∧
      ((b.block j).map I.subtype).pCoreIn 2 = sourceModule ((b.block j).map I.subtype) := by
  obtain ⟨⟨h⟩,⟨h'⟩⟩ := c.alternating_paired_setups b i j hij hs hi
  have hcore (n m : Fin b.size)
      (d : AlternatingPairSetup R ((b.block n).map I.subtype) ((b.block m).map I.subtype)) :
      ((b.block n).map I.subtype).pCoreIn 2 = sourceModule ((b.block n).map I.subtype) := by
    obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b n
    have hnc : ¬ (sourceModule ((b.block n).map I.subtype)).map
        (MulAut.conj x⁻¹).toMonoidHom ≤
        centralizer (sourceModule ((b.block n).map I.subtype) : Set G) := by
      rw [ambientModule_eq_literal] at hcomm
      exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
    exact congrArg (map ((b.block n).map I.subtype).subtype)
      (d.block_core_eq_module x (c.R_normal hx) hnc)
  exact ⟨hcore i j h,hcore j i h'⟩

/-- Independent point-stabilizer lifts and the original Sylow block exchanger,
all on the two original markings and inside the literal point centralizer. -/
theorem source_paired_borel_action_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    ∃ h : AlternatingPairSetup ((T : Subgroup G) ⊓ I)
        ((b.block i).map I.subtype) ((b.block j).map I.subtype),
    ∃ h' : AlternatingPairSetup ((T : Subgroup G) ⊓ I)
        ((b.block j).map I.subtype) ((b.block i).map I.subtype),
      (∀ k : (b.block i).map I.subtype, (k : G) ∈ Mc ↔
        h.action (inclusion le_sup_left k) 4 = 4) ∧
      (∀ k : (b.block j).map I.subtype, (k : G) ∈ Mc ↔
        h'.action (inclusion le_sup_left k) 4 = 4) ∧
      (∀ a : B, ∃ k : (b.block i).map I.subtype, (k : G) ∈ I ⊓ Mc ∧
        h.action (inclusion le_sup_left k) = a.val.val) ∧
      (∀ a : B, ∃ k : (b.block j).map I.subtype, (k : G) ∈ I ⊓ Mc ∧
        h'.action (inclusion le_sup_left k) = a.val.val) ∧
      ((T : Subgroup G) ⊓ I ≤ I ⊓ Mc) ∧
      ∃ t ∈ (T : Subgroup G) ⊓ I,
        ((b.block i).map I.subtype).map (MulAut.conj t).toMonoidHom =
          (b.block j).map I.subtype := by
  obtain ⟨z,hz,heq,hzS,hzR,hout,h,v,hv,hcentral,hpoint⟩ :=
    source_paired_block_point_marking hG T hempty hM hunique hmany hcard e hab
      H hH u hu I hI Λ c b i j hij hs hi
  obtain ⟨_,⟨h₂⟩⟩ := c.alternating_paired_setups b i j hij hs hi
  obtain ⟨_,_,_,_,_,_,h',_,_,_,hpoint'⟩ :=
    source_paired_block_point_marking hG T hempty hM hunique hmany hcard e hab
      H hH u hu I hI Λ c b j i hij.symm hs h₂.block
  have hR : (T : Subgroup G) ⊓ I ≤ I ⊓ Mc := by
    intro r hr
    refine ⟨hr.2,?_⟩
    rw [←heq]
    exact mem_centralizer_singleton_iff.mpr (hzR r hr)
  have hlift {K L : Subgroup G} (d : AlternatingPairSetup ((T : Subgroup G) ⊓ I) K L)
      (hK : K ≤ I)
      (hmark : ∀ k : K, (k : G) ∈ Mc ↔ d.action (inclusion le_sup_left k) 4 = 4)
      (a : B) : ∃ k : K, (k : G) ∈ I ⊓ Mc ∧
        d.action (inclusion le_sup_left k) = a.val.val := by
    have ha : a.val.val ∈ (K.subgroupOf (K ⊔ ChapterB.baumann ((T : Subgroup G) ⊓ I))).map
        d.action := d.block_image.symm ▸ a.val.property
    obtain ⟨k,hk,he⟩ := ha
    let kK : K := ⟨k,hk⟩
    have hact : d.action (inclusion le_sup_left kK) = a.val.val := he
    exact ⟨kK,⟨hK hk,(hmark kK).mpr (hact ▸ a.property)⟩,hact⟩
  obtain ⟨t,ht,_,he⟩ := c.pair_exchange b i j hij
  exact ⟨h,h',hpoint,hpoint',hlift h (map_subtype_le _) hpoint,
    hlift h' (map_subtype_le _) hpoint',hR,t,ht,he⟩


/-- The original source supplies all actors for the paired Borel section.
The markings remain the actual two block coordinates. -/
theorem source_paired_borel_irreducible
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    ∃ h : AlternatingPairSetup ((T : Subgroup G) ⊓ I)
        ((b.block i).map I.subtype) ((b.block j).map I.subtype),
    ∃ h' : AlternatingPairSetup ((T : Subgroup G) ⊓ I)
        ((b.block j).map I.subtype) ((b.block i).map I.subtype),
      (∀ k : (b.block i).map I.subtype, (k : G) ∈ Mc ↔
        h.action (inclusion le_sup_left k) 4 = 4) ∧
      (∀ k : (b.block j).map I.subtype, (k : G) ∈ Mc ↔
        h'.action (inclusion le_sup_left k) 4 = 4) ∧
      Nat.card (three.map h.borelMap ⊔ three.map h'.borelMap : Subgroup G) = 64 ∧
      Nat.card (line.map h.borelMap ⊔ line.map h'.borelMap : Subgroup G) = 4 ∧
      IsIrreducibleSection (I ⊓ Mc)
        (line.map h.borelMap ⊔ line.map h'.borelMap)
        (three.map h.borelMap ⊔ three.map h'.borelMap) := by
  obtain ⟨h,h',hp,hp',hl,hl',hR,t,ht,hKL⟩ := source_paired_borel_action_inputs
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  have hex : ∃ t ∈ I ⊓ Mc,
      (three.map h.borelMap).map (MulAut.conj t).toMonoidHom = three.map h'.borelMap :=
    ⟨t,hR ht,h.borel_three_map_conj h' hp hp' t (Mc.le_normalizer (hR ht).2) hKL⟩
  have hg := h.paired_borel_geometry h' (I ⊓ Mc) hl hl' hex
  exact ⟨h,h',hp,hp',hg.1,hg.2.1,
    h.paired_borel_irreducible_section h' (I ⊓ Mc) hl hl' hex⟩


/-- The embedded three-spaces and fixed lines are the literal source
intersections Ui ∩ Ri and centers Z(Ri), on the same action coordinates. -/
theorem source_paired_borel_flags
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    let K₁ := (b.block i).map I.subtype
    let K₂ := (b.block j).map I.subtype
    let X₁ := (pResidual 2 (K₁ ⊓ Mc : Subgroup G)).map (K₁ ⊓ Mc).subtype
    let X₂ := (pResidual 2 (K₂ ⊓ Mc : Subgroup G)).map (K₂ ⊓ Mc).subtype
    ∃ h : AlternatingPairSetup ((T : Subgroup G) ⊓ I) K₁ K₂,
    ∃ h' : AlternatingPairSetup ((T : Subgroup G) ⊓ I) K₂ K₁,
      (∀ k : K₁, (k : G) ∈ Mc ↔ h.action (inclusion le_sup_left k) 4 = 4) ∧
      (∀ k : K₂, (k : G) ∈ Mc ↔ h'.action (inclusion le_sup_left k) 4 = 4) ∧
      sourceModule K₁ ⊓ X₁.pCoreIn 2 = three.map h.borelMap ∧
      sourceModule K₂ ⊓ X₂.pCoreIn 2 = three.map h'.borelMap ∧
      (center (X₁.pCoreIn 2)).map (X₁.pCoreIn 2).subtype = line.map h.borelMap ∧
      (center (X₂.pCoreIn 2)).map (X₂.pCoreIn 2).subtype = line.map h'.borelMap ∧
      Nat.card (three.map h.borelMap ⊔ three.map h'.borelMap : Subgroup G) = 64 ∧
      Nat.card (line.map h.borelMap ⊔ line.map h'.borelMap : Subgroup G) = 4 ∧
      IsIrreducibleSection (I ⊓ Mc)
        (line.map h.borelMap ⊔ line.map h'.borelMap)
        (three.map h.borelMap ⊔ three.map h'.borelMap) := by
  obtain ⟨h,h',hp,hp',hcE,hcZ,hirr⟩ := source_paired_borel_irreducible
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  obtain ⟨z,hz,heq,hzS,hzR,hout,_⟩ := source_paired_block_point_marking
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  obtain ⟨_,_,_,_,_,hout',_⟩ := source_paired_block_point_marking
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b j i hij.symm hs h'.block
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  have hnc : ¬ (sourceModule ((b.block i).map I.subtype)).map
      (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule ((b.block i).map I.subtype) : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  obtain ⟨y,hy,hcomm'⟩ := c.exists_noncommuting_module b j
  have hnc' : ¬ (sourceModule ((b.block j).map I.subtype)).map
      (MulAut.conj y⁻¹).toMonoidHom ≤
      centralizer (sourceModule ((b.block j).map I.subtype) : Set G) := by
    rw [ambientModule_eq_literal] at hcomm'
    exact fun hh => hcomm' (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  have hf := h.central_point_flags x (c.R_normal hx) hnc z hzS hzR (heq.symm ▸ hout)
  have hf' := h'.central_point_flags y (c.R_normal hy) hnc' z hzS hzR (heq.symm ▸ hout')
  dsimp only at hf hf'
  rw [heq] at hf hf'
  exact ⟨h,h',hp,hp',hf.1,hf'.1,hf.2,hf'.2,hcE,hcZ,hirr⟩

/-- Original 14.6.9(k): Iz acts irreducibly on the literal E₀/Z₀;
both terms are Iz-invariant and have orders 64 and 4. -/
theorem source_paired_irreducible_section
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    let K₁ := (b.block i).map I.subtype
    let K₂ := (b.block j).map I.subtype
    let X₁ := (pResidual 2 (K₁ ⊓ Mc : Subgroup G)).map (K₁ ⊓ Mc).subtype
    let X₂ := (pResidual 2 (K₂ ⊓ Mc : Subgroup G)).map (K₂ ⊓ Mc).subtype
    let E₀ := (sourceModule K₁ ⊓ X₁.pCoreIn 2) ⊔ (sourceModule K₂ ⊓ X₂.pCoreIn 2)
    let Z₀ := (center (X₁.pCoreIn 2)).map (X₁.pCoreIn 2).subtype ⊔
      (center (X₂.pCoreIn 2)).map (X₂.pCoreIn 2).subtype
    Nat.card E₀ = 64 ∧ Nat.card Z₀ = 4 ∧
      I ⊓ Mc ≤ normalizer (E₀ : Set G) ∧
      I ⊓ Mc ≤ normalizer (Z₀ : Set G) ∧
      IsIrreducibleSection (I ⊓ Mc) Z₀ E₀ := by
  obtain ⟨h,h',hp,hp',hE,hE',hZ,hZ',hcE,hcZ,hirr⟩ := source_paired_borel_flags
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  have hEn := source_paired_commutator_normalized c b i j hij hs Mc
  have hZn := source_paired_center_normalized c b i j hij hs Mc
  rw [←h.borel_three_eq_commutator hp,←h'.borel_three_eq_commutator hp'] at hEn
  dsimp only
  rw [hE,hE',hZ,hZ']
  exact ⟨hcE,hcZ,hEn,by simpa only [hZ,hZ'] using hZn,hirr⟩

omit [Finite G] in
private theorem irreducible_section_subgroupOf
    (H S Z E : Subgroup G) (hSH : S ≤ H) (hEH : E ≤ H)
    (hi : IsIrreducibleSection S Z E) :
    IsIrreducibleSection (S.subgroupOf H) (Z.subgroupOf H) (E.subgroupOf H) := by
  have hZH : Z ≤ H := hi.1.trans hEH
  refine ⟨subgroupOf_mono H hi.1,?_,?_⟩
  · intro he
    apply hi.2.1
    have hm := congrArg (map H.subtype) he
    simpa only [map_subgroupOf_eq_of_le hZH,map_subgroupOf_eq_of_le hEH] using hm
  · intro W hZW hWE hn
    have hZW' : Z ≤ W.map H.subtype := by
      rw [←map_subgroupOf_eq_of_le hZH]
      exact map_mono hZW
    have hWE' : W.map H.subtype ≤ E := by
      rw [←map_subgroupOf_eq_of_le hEH]
      exact map_mono hWE
    have hn' : IsConjugateInvariantBy (W.map H.subtype) S := by
      intro s w hw
      obtain ⟨v,hv,rfl⟩ := hw
      let sH : H := ⟨s,hSH s.property⟩
      exact mem_map_of_mem H.subtype (hn ⟨sH,s.property⟩ v hv)
    rcases hi.2.2 (W.map H.subtype) hZW' hWE' hn' with he | he
    · left
      apply map_injective H.subtype_injective
      rwa [map_subgroupOf_eq_of_le hZH]
    · right
      apply map_injective H.subtype_injective
      rwa [map_subgroupOf_eq_of_le hEH]

omit [Finite G] in
private theorem normalizer_subgroupOf
    (H S E : Subgroup G) (hn : S ≤ normalizer (E : Set G)) :
    S.subgroupOf H ≤ normalizer (E.subgroupOf H : Set H) := by
  intro s hs
  apply mem_normalizer_iff.mpr
  intro v
  exact hn hs v


/-- The exact E₀/Z₀ section inside Mc, in the ambient type required by the
original omega-core quotient consumer. -/
theorem source_paired_irreducible_section_in_Mc
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    let K₁ := (b.block i).map I.subtype
    let K₂ := (b.block j).map I.subtype
    let X₁ := (pResidual 2 (K₁ ⊓ Mc : Subgroup G)).map (K₁ ⊓ Mc).subtype
    let X₂ := (pResidual 2 (K₂ ⊓ Mc : Subgroup G)).map (K₂ ⊓ Mc).subtype
    let E₀ := (sourceModule K₁ ⊓ X₁.pCoreIn 2) ⊔ (sourceModule K₂ ⊓ X₂.pCoreIn 2)
    let Z₀ := (center (X₁.pCoreIn 2)).map (X₁.pCoreIn 2).subtype ⊔
      (center (X₂.pCoreIn 2)).map (X₂.pCoreIn 2).subtype
    Nat.card (E₀.subgroupOf Mc) = 64 ∧ Nat.card (Z₀.subgroupOf Mc) = 4 ∧
      (I ⊓ Mc).subgroupOf Mc ≤ normalizer (E₀.subgroupOf Mc : Set Mc) ∧
      (I ⊓ Mc).subgroupOf Mc ≤ normalizer (Z₀.subgroupOf Mc : Set Mc) ∧
      IsIrreducibleSection ((I ⊓ Mc).subgroupOf Mc) (Z₀.subgroupOf Mc) (E₀.subgroupOf Mc) := by
  let K₁ := (b.block i).map I.subtype
  let K₂ := (b.block j).map I.subtype
  let X₁ := (pResidual 2 (K₁ ⊓ Mc : Subgroup G)).map (K₁ ⊓ Mc).subtype
  let X₂ := (pResidual 2 (K₂ ⊓ Mc : Subgroup G)).map (K₂ ⊓ Mc).subtype
  let E₀ := (sourceModule K₁ ⊓ X₁.pCoreIn 2) ⊔ (sourceModule K₂ ⊓ X₂.pCoreIn 2)
  let Z₀ := (center (X₁.pCoreIn 2)).map (X₁.pCoreIn 2).subtype ⊔
    (center (X₂.pCoreIn 2)).map (X₂.pCoreIn 2).subtype
  obtain ⟨hcE,hcZ,hnE,hnZ,hirr⟩ := source_paired_irreducible_section
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  have hEMc : E₀ ≤ Mc := sup_le
    (inf_le_right.trans ((pCoreIn_le 2 X₁).trans ((map_subtype_le _).trans inf_le_right)))
    (inf_le_right.trans ((pCoreIn_le 2 X₂).trans ((map_subtype_le _).trans inf_le_right)))
  have hZMc : Z₀ ≤ Mc := hirr.1.trans hEMc
  exact ⟨(Nat.card_congr (subgroupOfEquivOfLe hEMc).toEquiv).trans hcE,
    (Nat.card_congr (subgroupOfEquivOfLe hZMc).toEquiv).trans hcZ,
    normalizer_subgroupOf Mc (I ⊓ Mc) E₀ hnE,
    normalizer_subgroupOf Mc (I ⊓ Mc) Z₀ hnZ,
    irreducible_section_subgroupOf Mc (I ⊓ Mc) Z₀ E₀ inf_le_right hEMc hirr⟩

/-- The original source version with Ui = O₂(Ki), inside Mc. -/
theorem source_paired_core_section_in_Mc
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    let K₁ := (b.block i).map I.subtype
    let K₂ := (b.block j).map I.subtype
    let X₁ := (pResidual 2 (K₁ ⊓ Mc : Subgroup G)).map (K₁ ⊓ Mc).subtype
    let X₂ := (pResidual 2 (K₂ ⊓ Mc : Subgroup G)).map (K₂ ⊓ Mc).subtype
    let E₀ := (K₁.pCoreIn 2 ⊓ X₁.pCoreIn 2) ⊔ (K₂.pCoreIn 2 ⊓ X₂.pCoreIn 2)
    let Z₀ := (center (X₁.pCoreIn 2)).map (X₁.pCoreIn 2).subtype ⊔
      (center (X₂.pCoreIn 2)).map (X₂.pCoreIn 2).subtype
    Nat.card (E₀.subgroupOf Mc) = 64 ∧ Nat.card (Z₀.subgroupOf Mc) = 4 ∧
      (I ⊓ Mc).subgroupOf Mc ≤ normalizer (E₀.subgroupOf Mc : Set Mc) ∧
      (I ⊓ Mc).subgroupOf Mc ≤ normalizer (Z₀.subgroupOf Mc : Set Mc) ∧
      IsIrreducibleSection ((I ⊓ Mc).subgroupOf Mc) (Z₀.subgroupOf Mc) (E₀.subgroupOf Mc) := by
  obtain ⟨hU,hU'⟩ := source_paired_cores_eq_modules c b i j hij hs hi
  dsimp only
  rw [hU,hU']
  exact source_paired_irreducible_section_in_Mc hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI Λ c b i j hij hs hi

end CFSG.Quasithin.Chapter14.Section06
