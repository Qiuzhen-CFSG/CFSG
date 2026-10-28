module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.GeneratedSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.TorusSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.LocalFamily
public import Theory.GroupTheory.SylowNormalizedSupIndex
/-!
# The literal new local group in the double linear source

The adjusted torus actor gives a block stabilizer of index two inside the
new two-subgroup. The two conjugate blocks generate a normal subgroup
centralizing the independent nontrivial Sylow factor. Original local
maximality makes the indicated two-subgroup Sylow and puts the generated
group in gammaMax. The second natural block belongs to its intrinsic local
family on the exact original block stabilizer.

Source: Aschbacher–Smith 2.4.7, printed pp.540–541.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource LinearDouble
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G}
variable {d : MinimalBlockSetup M} {n : ℕ}

theorem DoubleLinearSourceSetup.adjusted_pair_geometry
    (c : DoubleLinearSourceSetup d M₀ n)
    (T : Sylow 2 G) (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀) (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (a : SourceTorusData c) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R₁ := elementaryAbelianMaxJ S ⊓ d.block.map d.H.subtype
    let B := S ⊓ normalizer (d.block.map d.H.subtype : Set G)
    let S₁ := M₀ ⊓ normalizer (R₁ : Set G)
    let K := c.second ⊔ c.second.map (MulAut.conj a.x⁻¹).toMonoidHom
    let X := K ⊔ S₁
    B ≤ S₁ ∧ B.relIndex S₁ = 2 ∧ a.x ∈ S₁ ∧
      K ≤ centralizer (R₁ : Set G) ∧ K ⊓ S₁ ≤ B ∧
      (K.subgroupOf X).Normal ∧ R₁ ≤ twoCore X := by
  let := c.field₁_field
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := elementaryAbelianMaxJ S
  let R₁ := R ⊓ d.block.map d.H.subtype
  let B := S ⊓ normalizer (d.block.map d.H.subtype : Set G)
  let S₁ := M₀ ⊓ normalizer (R₁ : Set G)
  let K := c.second ⊔ c.second.map (MulAut.conj a.x⁻¹).toMonoidHom
  let X := K ⊔ S₁
  change B ≤ S₁ ∧ B.relIndex S₁ = 2 ∧ a.x∈S₁ ∧ K≤centralizer (R₁:Set G) ∧
    K⊓S₁≤B ∧ (K.subgroupOf X).Normal ∧ R₁≤twoCore X
  have hBR := (c.core_pair T hST hSM hMT hi).1
  have hRS : R ≤ S := sSup_le (fun _ h => h.1)
  have hne : R₁ ≠ R ⊓ c.second := by
    intro he
    have hd := a.geometry.disjoint
    change Disjoint R₁ (R ⊓ c.second) at hd
    rw [←he] at hd
    exact a.geometry.nontrivial_first (disjoint_self.mp hd)
  have hB : B = S ⊓ S₁ := by
    have he := c.block_stabilizer_eq_factor_stabilizer hne
    change B = S ⊓ normalizer (R₁ : Set G) at he
    rw [he,show S ⊓ S₁ = S ⊓ normalizer (R₁ : Set G) by
      change S ⊓ (M₀ ⊓ normalizer (R₁ : Set G)) = _
      rw [←inf_assoc,inf_eq_left.mpr hSM]]
  have hBS : B ≤ S₁ := hB.le.trans inf_le_right
  have hxS : a.x ∈ S₁ := ⟨a.x_mem,a.geometry.fixes_first_sylow⟩
  have hiB : B.relIndex S₁ = 2 := by
    rw [hB]
    exact inf_relIndex_eq_two S M₀ S₁ inf_le_left hi a.x hxS a.x_outside
  have hUR : sourceModule (d.block.map d.H.subtype) ≤ R₁ :=
    le_inf (c.marked₁.module_le.trans_eq hBR) (map_subtype_le _)
  have hnc : ¬ (sourceModule (d.block.map d.H.subtype)).map
      (MulAut.conj a.x⁻¹).toMonoidHom ≤ centralizer (sourceModule (d.block.map d.H.subtype) : Set G) := by
    rw [a.first_mark]
    exact c.noncommuting
  have hc : K ≤ centralizer (R₁ : Set G) := by
    have hL : c.second ≤ centralizer (R₁ : Set G) := a.geometry.cross_first.trans (centralizer_le (show R₁ ≤ R₁ ⊔ a.borel.first.torus from le_sup_left))
    apply sup_le hL
    have hx := normalizer_le_normalizer_centralizer R₁ a.geometry.fixes_first_sylow
    have he : (centralizer (R₁:Set G)).map (MulAut.conj a.x⁻¹).toMonoidHom = centralizer (R₁:Set G) :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (centralizer (R₁:Set G) : Set G)).inv_mem hx)
    exact (map_mono hL).trans_eq he
  have hKS := c.generated_pair_sylow_le_stabilizer S₁ R₁ a.x hiB hxS a.x_outside hUR hnc hc
  have hn := c.generated_pair_normal S₁ a.x hBS hiB hxS a.x_outside
  have hRX : R₁ ≤ X := (le_inf ((inf_le_left.trans hRS).trans hSM) R₁.le_normalizer).trans le_sup_right
  have hXR : X ≤ normalizer (R₁ : Set G) := sup_le (hc.trans (Subgroup.centralizer_le_normalizer _)) inf_le_right
  have hRp : IsPGroup 2 R₁ := (d.S.isPGroup'.map d.H.subtype).to_le (inf_le_left.trans hRS)
  exact ⟨hBS,hiB,hxS,hc,hKS,hn,le_pCoreIn_of_normalizes hRp hRX hXR⟩


/-- The actual torus and index-two source give the full local pair,
maximal local family membership, Sylow subgroup and intrinsic local block. -/
theorem DoubleLinearSourceSetup.adjusted_pair_local_source
    (T : Sylow 2 G) (c : DoubleLinearSourceSetup d (T : Subgroup G) n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex (T : Subgroup G) = 2)
    (a : SourceTorusData c) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R₁ := elementaryAbelianMaxJ S ⊓ d.block.map d.H.subtype
    let B := S ⊓ normalizer (d.block.map d.H.subtype : Set G)
    let S₁ := (T : Subgroup G) ⊓ normalizer (R₁ : Set G)
    let K := c.second ⊔ c.second.map (MulAut.conj a.x⁻¹).toMonoidHom
    let X := K ⊔ S₁
    X ∈ gammaMax (Chapter1.He G) M ∧
      (B,c.second ⊔ B) ∈ localPairsIn (Chapter1.He G) M X ∧
      (∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = S₁) ∧
      c.second.subgroupOf X ∈ Chapter1.L X (B.subgroupOf X) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := elementaryAbelianMaxJ S
  let R₁ := R ⊓ d.block.map d.H.subtype
  let B := S ⊓ normalizer (d.block.map d.H.subtype : Set G)
  let S₁ := (T : Subgroup G) ⊓ normalizer (R₁ : Set G)
  let K := c.second ⊔ c.second.map (MulAut.conj a.x⁻¹).toMonoidHom
  let X := K ⊔ S₁
  change X∈gammaMax (Chapter1.He G) M ∧ (B,c.second⊔B)∈localPairsIn (Chapter1.He G) M X ∧
    (∃ P:Sylow 2 X,(P:Subgroup X).map X.subtype=S₁) ∧ c.second.subgroupOf X∈Chapter1.L X (B.subgroupOf X)
  obtain ⟨hBS,hiB,_,_,_,_,hRcore⟩ := c.adjusted_pair_geometry T hST hST le_rfl hi a
  change B≤S₁ at hBS
  change B.relIndex S₁=2 at hiB
  change R₁≤twoCore X at hRcore
  obtain ⟨hB,hRB,_⟩ := c.block_stabilizer_beta hG T hM hTM hu hST hST le_rfl hi
  change B∈beta M at hB
  change R≤B at hRB
  have hLX : c.second ≤ X := le_sup_left.trans le_sup_left
  have hBX : B≤X := hBS.trans le_sup_right
  have hp : (B,c.second⊔B)∈localPairsIn (Chapter1.He G) M X :=
    ⟨c.block_stabilizer_local_pair hG T hM hTM hu hST hST le_rfl hi,sup_le hLX hBX⟩
  have hXgamma : X∈gamma (Chapter1.He G) M :=
    ⟨fun he => a.geometry.nontrivial_first (bot_unique (he ▸ hRcore)),⟨_,hp⟩⟩
  have hS₁beta : S₁∈beta M := beta_mono hB hBS (T.isPGroup'.to_le inf_le_left)
  have hcard : Nat.card S₁ = Nat.card S := by
    have h₁ := (B.subgroupOf S₁).card_mul_index
    have h₂ := (B.subgroupOf S).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hBS).toEquiv] at h₁
    rw [Nat.card_congr (subgroupOfEquivOfLe (show B≤S from inf_le_left)).toEquiv] at h₂
    change Nat.card B * B.relIndex S₁ = Nat.card S₁ at h₁
    change Nat.card B * B.relIndex S = Nat.card S at h₂
    have hiS : B.relIndex S=2 := c.block_stabilizer_index
    rw [hiB] at h₁
    rw [hiS] at h₂
    exact h₁.symm.trans h₂
  have hb : Nat.card S≤twoPart X := hcard ▸ beta_card_le_twoPart hS₁beta le_sup_right
  obtain ⟨hc,hXmax⟩ := (lemma_2_3_7_1 T hTM hu (d.mem_gammaEvenZero.1.elim (fun h => h.1.1) (fun h => h.1)) d.S hST hi).2 X hXgamma hb
  have hSylow := exists_sylow_of_card (show S₁≤X from le_sup_right) (hcard.trans hc.symm)
  have hBp : IsPGroup 2 B := (d.S.isPGroup'.map d.H.subtype).to_le inf_le_left
  have hBN : B≤normalizer (c.second : Set G) := c.block_stabilizer_normalizes_second
  obtain ⟨P,hP⟩ := hBp.exists_sylow_sup_of_coprime_index c.second B hBN
    (a.borel.second.sylow : Subgroup c.second) a.borel.second.sylow.not_dvd_index
    (a.borel.second.sylow_eq.le.trans (inf_le_left.trans hRB))
  have hnot : ¬ ChapterC.IsAlternatingBlock c.second 3 := by
    intro h3
    have hc : 2^(n*2)=4 := by rw [←c.second_type.module_card,h3.module_card_odd (by decide)]; norm_num
    have hn := c.second_type.1
    have hlow : 16≤2^(n*2) := Nat.pow_le_pow_right (by decide : 1≤2) (by omega : 4≤n*2)
    omega
  have hlocal := ChapterC.Section05.NormalizerControl.noncubic_mem_local_family c.second B
    (Or.inl ⟨n,c.second_type⟩) hnot hBN P hP
  exact ⟨hXmax,hp,hSylow,(Chapter1.mem_LIn_iff_subgroupOf hBX hLX).mp ⟨hLX,hlocal⟩⟩

end CFSG.Quasithin.Chapter2
