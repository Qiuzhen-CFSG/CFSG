module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterTorus
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount
public import Theory.GroupAction.PerfectFixedCover

/-!
# Cartan-fixed native triality neighbors

A native rank-one parabolic has two Bruhat cells. In the nonidentity cell,
a Cartan-fixed Borel coset yields a coprime displacement in the positive
group. Fixed-coset lifting removes that displacement, and the public native
unipotent torus-normalizer theorem leaves just the marked Weyl coset.
The full Cartan and both unequal parabolic types are retained, including q=4.

Source: Aschbacher--Smith F.4.10,16, pp.279,282; GLS3 §§2.3--2.4.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
open Subgroup
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat
open CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open scoped Pointwise

private theorem reflection_normalizes (m : ℕ) (hm : 0 < m) (s : Node) :
    simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) s ∈
      normalizer (torus (binaryParameters m hm) : Set _) := by
  rw [←weylRepresentative_simple _ (binaryParameters_prime m hm)]
  exact RelativeNormalizer.weylRepresentative_normalizes_torus _ rfl _

private theorem rank_one_cells (m : ℕ) (hm : 0 < m) (s : Node)
    (g : BinaryCarrier m hm) (hg : g ∈ parabolic (binaryParameters m hm) s) :
    g ∈ borel (binaryParameters m hm) ∨
      ∃ a ∈ borel (binaryParameters m hm), ∃ b ∈ borel (binaryParameters m hm),
        g = a * simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) s * b := by
  obtain ⟨w,hw,hg⟩ := (FixedDescent.mem_parabolic_iff_exists_cell m hm s g).mp hg
  rcases (FoldedCellGeometry.rootRepresentative_mem_parabolicWeyl_iff s w).mp hw with hw | hw
  · left
    rwa [hw,cell_one _ (binaryParameters_prime m hm)] at hg
  · right
    rw [hw] at hg
    obtain ⟨a,ha,b,hb,he⟩ := (mem_cell_iff _ (binaryParameters_prime m hm) _ g).mp hg
    exact ⟨a,ha,b,hb,by simpa only [weylRepresentative_simple _ (binaryParameters_prime m hm)] using he⟩

private theorem fixed_coset_in_cell (m : ℕ) (hm : 0 < m) (hm2 : 1 < m) (s : Node)
    (u : BinaryCarrier m hm) (hu : u ∈ unipotent (binaryParameters m hm))
    (hf : ∀ t ∈ torus (binaryParameters m hm),
      (simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) s)⁻¹ * u⁻¹ * t * u * (simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) s) ∈ borel (binaryParameters m hm)) :
    (simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) s)⁻¹ * u * (simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) s) ∈ borel (binaryParameters m hm) := by
  let w := (simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) s)
  let T := torus (binaryParameters m hm)
  let U := unipotent (binaryParameters m hm)
  let B := borel (binaryParameters m hm)
  have hw : w ∈ normalizer (T : Set (BinaryCarrier m hm)) := reflection_normalizes m hm s
  have hTU : T ≤ normalizer (U : Set (BinaryCarrier m hm)) :=
    (torus_le_borel (binaryParameters m hm)).trans (borel_le_normalizer_unipotent (binaryParameters m hm) (binaryParameters_prime m hm))
  have hTB : T ≤ B := torus_le_borel (binaryParameters m hm)
  have htw (t : BinaryCarrier m hm) (ht : t ∈ T) : w⁻¹*t*w ∈ B := by
    apply hTB
    simpa only [inv_inv] using (mem_normalizer_iff.mp (inv_mem hw) t).mp ht
  let N : Subgroup (BinaryCarrier m hm) := U ⊓ B.comap (MulAut.conj w⁻¹).toMonoidHom
  have hTN : T ≤ normalizer (N : Set (BinaryCarrier m hm)) := by
    rw [le_normalizer_iff]
    intro t ht x hx
    refine ⟨(mem_normalizer_iff.mp (hTU ht) x).mp hx.1,?_⟩
    change w⁻¹*(t*x*t⁻¹)*w ∈ B
    have hxB : w⁻¹*x*w ∈ B := hx.2
    convert B.mul_mem (B.mul_mem (htw t ht) hxB) (B.inv_mem (htw t ht)) using 1
    group
  let α : T →* MulAut (BinaryCarrier m hm) := MulAut.conj.comp T.subtype
  let act : MulDistribMulAction T (BinaryCarrier m hm) := MulDistribMulAction.compHom _ α
  let : SMul T (BinaryCarrier m hm) := act.toSMul
  let : MulDistribMulAction T (BinaryCarrier m hm) := act
  let : IsInvariant T (BinaryCarrier m hm) N := ⟨fun t x => by
    change x ∈ N ↔ t.val*x*t.val⁻¹ ∈ N
    exact mem_normalizer_iff.mp (hTN t.property) x⟩
  have hsolv : Group.IsSolvable N := by
    let : Group.IsNilpotent N := ((unipotent_isPGroup_binary (binaryParameters m hm) (binaryParameters_prime m hm)).to_le (show N ≤ unipotent (binaryParameters m hm) from inf_le_left)).isNilpotent
    infer_instance
  have hcopU : (Nat.card T).Coprime (Nat.card U) := by
    change (Nat.card (torus (binaryParameters m hm))).Coprime (Nat.card (unipotent (binaryParameters m hm)))
    rw [FixedCellCount.card_unipotent, binaryParameters_q, ←pow_mul]
    exact (Nat.coprime_two_right.mpr
      (by rw [TorusCoordinates.card_torus _ rfl]; exact TorusCoordinates.odd_torus_order _ rfl)).pow_right _
  have hcop : (Nat.card T).Coprime (Nat.card N) :=
    hcopU.of_dvd_right (card_dvd_of_le (show N ≤ U from inf_le_left))
  obtain ⟨n,hn⟩ := Theory.GroupAction.exists_fixed_mul_of_solvable_coprime_displacement
    N hsolv hcop u (fun t => by
      refine ⟨U.mul_mem (U.inv_mem hu) ((mem_normalizer_iff.mp (hTU t.property) u).mp hu),?_⟩
      change w⁻¹*(u⁻¹*(t.val*u*t.val⁻¹))*w ∈ B
      convert B.mul_mem (hf t.val t.property) (htw t.val⁻¹ (inv_mem t.property)) using 1
      dsimp [w]
      group)
  have hcent : u*n.val ∈ centralizer (T : Set (BinaryCarrier m hm)) := by
    intro t ht
    have hh := hn (⟨t,ht⟩ : T)
    change t*(u*n.val)*t⁻¹=u*n.val at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh)
  have hone : u*n.val=1 := TrialityOuterTorus.unipotent_torus_normalizer_trivial
    m hm hm2 _ (U.mul_mem hu n.property.1) (centralizer_le_normalizer _ hcent)
  have huN : u ∈ N := by
    rw [eq_inv_of_mul_eq_one_left hone]
    exact N.inv_mem n.property
  exact huN.2

/-- The full Cartan fixes exactly the two marked Borel cosets in either full
native parabolic, for every nonbinary parameter, including q=4. -/
theorem parabolic_fixed_coset (m : ℕ) (hm : 0 < m) (hm2 : 1 < m) (s : Node)
    (g : BinaryCarrier m hm) (hg : g ∈ parabolic (binaryParameters m hm) s)
    (hf : ∀ t ∈ torus (binaryParameters m hm), g⁻¹*t*g ∈ borel (binaryParameters m hm)) :
    g ∈ borel (binaryParameters m hm) ∨ (simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) s)*g ∈ borel (binaryParameters m hm) := by
  rcases rank_one_cells m hm s g hg with h | ⟨a,ha,b,hb,rfl⟩
  · exact Or.inl h
  right
  have hprod : a ∈ (unipotent (binaryParameters m hm) : Set (BinaryCarrier m hm)) *
      (torus (binaryParameters m hm) : Set (BinaryCarrier m hm)) := by
    rw [←borel_eq_mul (binaryParameters m hm) (binaryParameters_prime m hm)]
    exact ha
  obtain ⟨u,hu,t,ht,rfl⟩ := hprod
  let w := (simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) s)
  have hw2 : w*w=1 := by
    simpa only [w,←pow_two] using simpleRepresentative_sq (binaryParameters m hm) (binaryParameters_prime m hm) s
  have hwi : w⁻¹=w := inv_eq_of_mul_eq_one_right hw2
  have htw : w⁻¹*t*w ∈ borel (binaryParameters m hm) := by
    apply torus_le_borel (binaryParameters m hm)
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (inv_mem (reflection_normalizes m hm s)) t).mp ht
  let b' := w⁻¹*t*w*b
  have hb' : b' ∈ borel (binaryParameters m hm) := mul_mem htw hb
  have he : u*t*w*b=u*w*b' := by dsimp [b']; group
  have hf' : ∀ z ∈ torus (binaryParameters m hm), w⁻¹*u⁻¹*z*u*w ∈ borel (binaryParameters m hm) := by
    intro z hz
    have hh := hf z hz
    change (u*t*w*b)⁻¹*z*(u*t*w*b) ∈ borel (binaryParameters m hm) at hh
    rw [he] at hh
    convert (borel (binaryParameters m hm)).mul_mem ((borel (binaryParameters m hm)).mul_mem hb' hh) (inv_mem hb') using 1
    group
  have huB := fixed_coset_in_cell m hm hm2 s u hu hf'
  change w⁻¹*u*w ∈ borel (binaryParameters m hm) at huB
  change w*(u*t*w*b) ∈ borel (binaryParameters m hm)
  rw [he]
  convert (borel (binaryParameters m hm)).mul_mem huB hb' using 1
  rw [hwi]
  group

end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
