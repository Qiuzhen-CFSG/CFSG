module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.PairOrbitCertificate
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.HexadOrbits

/-!
# The three native point–line orbits

The checked pair forest supplies literal M₂₂ transporters fixing the marked
hexad. Its root calculations give incidence, adjacency to all five points,
and exactly three adjacent points. Conjugating the same actions proves
existence, realization and transitivity for every native hexad and pair.
These are the native inputs to the unchanged ambient point–line orbit fields.
Source: Aschbacher–Segev (1991), (5.3)(3), p.600.
-/
public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativePairs
open Sporadic.Mathieu SourceCycleBase
open scoped Pointwise

private theorem exists_index (L : Pair) : ∃ i, pairAt i = L.val := by
  obtain ⟨x,y,hxy,he⟩ := Finset.card_eq_two.mp L.property
  exact ⟨lookup x y,(lookup_spec x y hxy).trans he.symm⟩

theorem exists_transport (i : Fin 231) : ∃ g : M22,
    g • m22Hexad123 = m22Hexad123 ∧ g • pairAt (seed (root i)) = pairAt i := by
  generalize hn : depth i = n
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    by_cases hz : depth i = 0
    · exact ⟨1,one_smul _ _,(one_smul _ _).trans (congrArg pairAt ((forest i).1 hz).symm)⟩
    · obtain ⟨g,hg,hgi⟩ := ih (depth (parent i)) (by have := ((forest i).2 hz).1; omega) (parent i) rfl
      refine ⟨generator (letter i)*g,?_,?_⟩
      · rw [mul_smul,hg,generator_fixes]
      · rw [mul_smul,←((forest i).2 hz).2.1,hgi]
        change (pairAt (parent i)).image (generator (letter i)).val = pairAt i
        rw [show (generator (letter i)).val = table (letter i) from funext (generator_apply _)]
        exact ((forest i).2 hz).2.2

private noncomputable def hexadEquiv (g : M22) : Hexad ≃ Hexad where
  toFun := NativeHexads.smulHexad g
  invFun := NativeHexads.smulHexad g⁻¹
  left_inv B := Subtype.ext (inv_smul_smul g B.val)
  right_inv B := Subtype.ext (smul_inv_smul g B.val)

@[expose] noncomputable def count (B : Finset (Fin 22)) (L : Finset (Fin 22)) : Nat :=
  Nat.card {C : Hexad // L ⊆ C.val ∧ (C.val ∩ B).card = 2}

theorem count_transport (g : M22) (B L : Finset (Fin 22)) :
    count (g • B) (g • L) = count B L := by
  symm
  apply Nat.card_congr
  apply (hexadEquiv g).subtypeEquiv
  intro C
  change (L ⊆ C.val ∧ (C.val ∩ B).card = 2) ↔
    (g • L ⊆ g • C.val ∧ ((g • C.val) ∩ (g • B)).card = 2)
  rw [Finset.smul_finset_subset_smul_finset_iff,NativeHexads.inter_card_smul]

private theorem seed_counts (i : Fin 3) : count m22Hexad123 (pairAt (seed i)) = (![4,5,3] : Fin 3 → Nat) i := by
  unfold count
  rw [←Nat.card_congr (NativeHexads.indexEquiv.subtypeEquiv
    (p := fun j => pairAt (seed i) ⊆ m22BlockAt j ∧ (m22BlockAt j ∩ m22Hexad123).card = 2)
    (q := fun C => pairAt (seed i) ⊆ C.val ∧ (C.val ∩ m22Hexad123).card = 2) (fun j => by rw [NativeHexads.indexEquiv_val]))]
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  exact root_counts i

/-- Three native point–line patterns, retaining literal incidence and the
number of neighboring hexads. -/
@[expose] def Pattern (i : Fin 3) (B : Finset (Fin 22)) (L : Finset (Fin 22)) : Prop :=
  match i.val with
  | 0 => L ⊆ B
  | 1 => ∀ C : Hexad, L ⊆ C.val → (C.val ∩ B).card = 2
  | _ => count B L = 3

theorem pattern_transport (g : M22) (i : Fin 3) (B L : Finset (Fin 22)) :
    Pattern i (g • B) (g • L) ↔ Pattern i B L := by
  fin_cases i
  · exact Finset.smul_finset_subset_smul_finset_iff
  · change (∀ C : Hexad, g • L ⊆ C.val → (C.val ∩ (g • B)).card = 2) ↔
      (∀ C : Hexad, L ⊆ C.val → (C.val ∩ B).card = 2)
    constructor
    · intro hh C hC
      have he := hh (NativeHexads.smulHexad g C) (Finset.smul_finset_subset_smul_finset hC)
      exact (NativeHexads.inter_card_smul g C.val B).symm.trans he
    · intro hh C hC
      have hs : L ⊆ g⁻¹ • C.val := by
        have ht := Finset.smul_finset_subset_smul_finset (a := g⁻¹) hC
        simpa only [inv_smul_smul] using ht
      have he := hh (NativeHexads.smulHexad g⁻¹ C) hs
      have hcard := NativeHexads.inter_card_smul g⁻¹ C.val (g • B)
      rw [inv_smul_smul] at hcard
      exact hcard.symm.trans he
  · exact congrArg (· = 3) (count_transport g B L) |>.to_iff

private theorem seed_pattern (i : Fin 3) : Pattern i m22Hexad123 (pairAt (seed i)) := by
  fin_cases i
  · exact (roots_pattern 0).1 rfl
  · intro C hC
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp C.property
    rw [←hj] at hC ⊢
    exact (roots_pattern 1).2.1 rfl j hC
  · exact seed_counts 2

private theorem seed_pattern_unique (i j : Fin 3) (hh : Pattern i m22Hexad123 (pairAt (seed j))) : i = j := by
  fin_cases i <;> fin_cases j
  all_goals try rfl
  · change pairAt (seed 1) ⊆ m22Hexad123 at hh
    exact (by decide +kernel : ¬ pairAt (seed 1) ⊆ m22Hexad123) hh |>.elim
  · change pairAt (seed 2) ⊆ m22Hexad123 at hh
    exact (by decide +kernel : ¬ pairAt (seed 2) ⊆ m22Hexad123) hh |>.elim
  · have he := hh ⟨m22Hexad123,m22Hexad123_mem⟩ ((roots_pattern 0).1 rfl)
    have hc : m22Hexad123.card = 6 := m22Block_card _ m22Hexad123_mem
    simp only [Finset.inter_self,hc] at he
    omega
  · have hn := seed_counts 2
    have hall : ∀ j : Fin 77, pairAt (seed 2) ⊆ m22BlockAt j →
        (m22BlockAt j ∩ m22Hexad123).card = 2 := by
      intro j hj
      exact hh ⟨m22BlockAt j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩ hj
    exact (root_two_not_all hall).elim
  · have hc := seed_counts 0
    change count m22Hexad123 (pairAt (seed 0)) = 3 at hh
    norm_num at hc
    omega
  · have hc := seed_counts 1
    change count m22Hexad123 (pairAt (seed 1)) = 3 at hh
    norm_num at hc
    omega

private theorem standard_orbit (L : Pair) : ∃ i : Fin 3, ∃ g : M22,
    g • m22Hexad123 = m22Hexad123 ∧ g • pairAt (seed i) = L.val := by
  obtain ⟨j,hj⟩ := exists_index L
  obtain ⟨g,hg,hgi⟩ := exists_transport j
  exact ⟨root j,g,hg,hgi.trans hj⟩

/-- Every native pair has exactly one of the three source types. -/
theorem pattern_exists (B : Hexad) (L : Pair) : ∃ i : Fin 3, Pattern i B.val L.val := by
  obtain ⟨k,hk⟩ := exists_smul_m22Hexad123_eq B.property
  let L' : Pair := ⟨k⁻¹ • L.val,by simpa using L.property⟩
  obtain ⟨i,g,hg,hgL⟩ := standard_orbit L'
  refine ⟨i,?_⟩
  have hp := (pattern_transport g i m22Hexad123 (pairAt (seed i))).mpr (seed_pattern i)
  rw [hg,hgL] at hp
  have hh := (pattern_transport k i m22Hexad123 L'.val).mpr hp
  simpa only [hk,L',smul_inv_smul] using hh

/-- Native pairs of the same source type have a transporter fixing the hexad. -/
theorem pattern_orbit (B : Hexad) (L K : Pair) (i : Fin 3)
    (hL : Pattern i B.val L.val) (hK : Pattern i B.val K.val) :
    ∃ g : M22, g • B.val = B.val ∧ g • L.val = K.val := by
  obtain ⟨k,hk⟩ := exists_smul_m22Hexad123_eq B.property
  let L' : Pair := ⟨k⁻¹ • L.val,by simpa using L.property⟩
  let K' : Pair := ⟨k⁻¹ • K.val,by simpa using K.property⟩
  obtain ⟨j,g,hg,hgL⟩ := standard_orbit L'
  obtain ⟨j',f,hf,hfK⟩ := standard_orbit K'
  have typeL : Pattern i m22Hexad123 L'.val := by
    have hh := (pattern_transport k⁻¹ i B.val L.val).mpr hL
    simpa only [←hk,inv_smul_smul] using hh
  have typeK : Pattern i m22Hexad123 K'.val := by
    have hh := (pattern_transport k⁻¹ i B.val K.val).mpr hK
    simpa only [←hk,inv_smul_smul] using hh
  have hij : i = j := seed_pattern_unique i j ((pattern_transport g i _ _).mp (by rw [hg,hgL]; exact typeL))
  have hij' : i = j' := seed_pattern_unique i j' ((pattern_transport f i _ _).mp (by rw [hf,hfK]; exact typeK))
  have he : j = j' := hij.symm.trans hij'
  refine ⟨k*(f*g⁻¹)*k⁻¹,?_,?_⟩
  · rw [mul_smul,mul_smul,←hk,inv_smul_smul,mul_smul,inv_smul_eq_iff.mpr hg.symm,hf]
  · change g • pairAt (seed j) = k⁻¹ • L.val at hgL
    change f • pairAt (seed j') = k⁻¹ • K.val at hfK
    rw [mul_smul,mul_smul,←hgL,mul_smul,inv_smul_smul,he,hfK,smul_inv_smul]

theorem pattern_realized (B : Hexad) (i : Fin 3) : ∃ L : Pair, Pattern i B.val L.val := by
  obtain ⟨k,hk⟩ := exists_smul_m22Hexad123_eq B.property
  refine ⟨⟨k • pairAt (seed i),by simpa using pair_card (seed i)⟩,?_⟩
  rw [←hk]
  exact (pattern_transport k i _ _).mpr (seed_pattern i)

theorem pattern_orbit_general (B C : Hexad) (L K : Pair) (i : Fin 3)
    (hL : Pattern i B.val L.val) (hK : Pattern i C.val K.val) :
    ∃ g : M22, g • B.val = C.val ∧ g • L.val = K.val := by
  obtain ⟨b,hb⟩ := exists_smul_m22Hexad123_eq B.property
  obtain ⟨c,hc⟩ := exists_smul_m22Hexad123_eq C.property
  let k := c*b⁻¹
  have hk : k • B.val = C.val := by rw [←hb,mul_smul,inv_smul_smul,hc]
  let L' : Pair := ⟨k • L.val,by simpa using L.property⟩
  have hp : Pattern i C.val L'.val := by
    rw [←hk]
    exact (pattern_transport k i _ _).mpr hL
  obtain ⟨g,hg,hgL⟩ := pattern_orbit C L' K i hp hK
  exact ⟨g*k,by rw [mul_smul,hk,hg],by rw [mul_smul]; exact hgL⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativePairs
