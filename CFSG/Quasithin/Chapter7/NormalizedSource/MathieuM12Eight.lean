module
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Inner
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.Representation.BinaryOffender.SylowTransport
/-!
# Elementary eights on the native M12 heart

An elementary eight saturates the eight noncommuting buckets in the verified
M12 Sylow coordinates. Three of those buckets supply six independent rows
of displacement equations. The displayed inverse matrices prove that four
coordinates determine any common fixed vector. Sylow conjugacy then gives
fixed codimension at least six for every native elementary eight.

All finite certificates are checked by the kernel. The generator is retained
in MathieuM12Eight/source/generate.py; it uses the existing Sylow words and
the literal deleted-permutation heart coordinates.
Source: Aschbacher--Smith H.11.1 and Table 7.2.1, printed pp.392,698.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM12Eight
open ChapterH.Section10To12 ChapterH.Section10To12.M12Calculations Sporadic.Mathieu
open M12SmallPair M12SmallPair.SylowAutomorphismGroup
open SmallModuleRanks.M12Certificate
open scoped Matrix
@[expose] def actor : Fin 11 → Fin 64 := ![4,35,17,22,22,22,5,40,53,7,9]
@[expose] def rows : Fin 11 → Fin 10 → BitVec 10 := ![![1023,989,1023,999,999,989,703,1023,703,1023],![5,34,5,0,0,34,320,640,320,640],![131,0,518,74,274,989,74,131,274,518],![769,266,388,266,304,304,703,388,0,769],![769,266,388,266,304,304,703,388,0,769],![769,266,388,266,304,304,703,388,0,769],![894,1023,507,1023,1023,1023,703,894,703,507],![521,74,140,0,999,296,74,140,296,521],![37,989,37,104,304,0,104,672,304,672],![0,66,0,24,24,288,66,640,288,640],![8,42,8,0,999,42,8,648,8,648]]
@[expose] def disp (k : Fin 11) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun i j => if (rows k i).getLsb j then 1 else 0
set_option maxRecDepth 4096 in
theorem native_disp (k : Fin 11) : displacementMatrix (element (actor k)).val.val = disp k := by
  fin_cases k <;> decide +kernel
@[expose] def select : Fin 5 → Fin 5 → Fin 6 → Fin 30 := ![![![0,1,3,6,10,20],![0,1,3,6,10,20],![0,1,3,6,10,20],![0,1,3,6,10,21],![0,1,3,6,10,20]],![![0,1,3,6,10,13],![0,1,3,6,10,13],![0,1,3,6,10,13],![0,1,3,6,10,13],![0,1,3,6,10,13]],![![0,1,3,6,10,11],![0,1,3,6,10,11],![0,1,3,6,10,11],![0,1,3,6,10,11],![0,1,3,6,10,11]],![![0,1,3,6,10,11],![0,1,3,6,10,11],![0,1,3,6,10,11],![0,1,3,6,10,11],![0,1,3,6,10,11]],![![0,1,3,6,10,11],![0,1,3,6,10,11],![0,1,3,6,10,11],![0,1,3,6,10,11],![0,1,3,6,10,11]]]
@[expose] def free : Fin 5 → Fin 5 → Fin 4 → Fin 10 := ![![![0,1,3,6],![0,1,3,6],![0,3,6,7],![0,1,3,7],![0,1,6,7]],![![0,1,2,3],![0,1,2,3],![0,1,2,3],![0,1,2,3],![0,1,2,3]],![![0,1,2,3],![0,1,2,3],![0,1,2,3],![0,1,2,3],![0,1,2,3]],![![0,1,2,3],![0,1,2,3],![0,1,2,3],![0,1,2,3],![0,1,2,3]],![![0,1,2,3],![0,1,2,3],![0,1,2,3],![0,1,2,3],![0,1,2,3]]]
@[expose] def inverseRows : Fin 5 → Fin 5 → Fin 10 → BitVec 10 := ![![![64,128,80,256,261,131,512,97,521,127],![64,128,80,256,261,131,512,382,521,352],![64,51,80,128,133,48,256,512,265,542],![64,128,80,256,261,131,160,512,169,542],![64,128,80,32,37,131,256,512,265,542]],![![64,128,256,512,517,131,672,208,681,414],![64,128,256,512,517,131,672,208,681,414],![64,128,256,512,517,131,672,208,681,414],![64,128,256,512,517,131,672,208,681,414],![64,128,256,512,517,131,672,208,681,414]],![![64,128,256,512,517,131,681,958,672,752],![64,128,256,512,517,131,681,958,672,752],![64,128,256,512,517,131,681,958,672,752],![64,128,256,512,517,131,681,958,672,752],![64,128,256,512,517,131,681,958,672,752]],![![64,128,256,512,517,131,681,958,672,752],![64,128,256,512,517,131,681,958,672,752],![64,128,256,512,517,131,681,958,672,752],![64,128,256,512,517,131,681,958,672,752],![64,128,256,512,517,131,681,958,672,752]],![![64,128,256,512,517,131,681,958,672,752],![64,128,256,512,517,131,681,958,672,752],![64,128,256,512,517,131,681,958,672,752],![64,128,256,512,517,131,681,958,672,752],![64,128,256,512,517,131,681,958,672,752]]]
@[expose] def actors (a b : Fin 5) : Fin 3 → Fin 11 := ![0,⟨a.val+1,by omega⟩,⟨b.val+6,by omega⟩]
@[expose] def test (a b : Fin 5) : Matrix (Fin 10) (Fin 10) (ZMod 2) := fun i j =>
  if hi : i.val < 6 then
    let n := select a b ⟨i.val,hi⟩
    disp (actors a b ⟨n.val / 10, by omega⟩) ⟨n.val % 10, by omega⟩ j
  else if j = free a b ⟨i.val-6,by omega⟩ then 1 else 0
@[expose] def inv (a b : Fin 5) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun i j => if (inverseRows a b i).getLsb j then 1 else 0
set_option maxRecDepth 4096 in
theorem inverse_certificate (a b : Fin 5) : inv a b * test a b = 1 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

private theorem cover_hits_every_part {A : Type*} [Group A] [Finite A]
    {n m : ℕ} (b : Fin n → Fin m → A)
    (hcover : ∀ g : A, g ^ 2 = 1 → ∃ c a, b c a = g)
    (huniq : ∀ c a a', b c a * b c a' = b c a' * b c a → b c a = b c a')
    (E : Subgroup A) (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = n)
    (c : Fin n) : ∃ a, b c a ∈ E := by
  classical
  have hex (g : E) : ∃ c a, b c a = g.val :=
    hcover g.val (congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p g))
  let f : E → Fin n := fun g => (hex g).choose
  have hf : Function.Injective f := by
    intro g h he
    obtain ⟨a,ha⟩ := (hex g).choose_spec
    obtain ⟨a',ha'⟩ := (hex h).choose_spec
    change b (f g) a = g.val at ha
    change b (f h) a' = h.val at ha'
    rw [←he] at ha'
    apply Subtype.ext
    rw [←ha,←ha']
    apply huniq
    rw [ha,ha']
    exact congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm g h)
  have hs : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,by simpa using hcard⟩).2
  obtain ⟨g,hg⟩ := hs c
  obtain ⟨a,ha⟩ := (hex g).choose_spec
  change b (f g) a = g.val at ha
  rw [hg] at ha
  exact ⟨a,ha.symm ▸ g.property⟩

private theorem sylow_hits_bucket (E : Subgroup sylowCandidate)
    (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 8) (c : Fin 8) :
    ∃ a, element (bucket c a) ∈ E := by
  apply cover_hits_every_part (fun c a => element (bucket c a)) ?_ ?_ E hE hcard c
  · intro g hg
    obtain ⟨i,rfl⟩ := element_surjective g
    have hs : multiply i i = 0 := element_injective (by
      rw [element_multiply,element_zero,←pow_two]
      exact hg)
    exact ⟨(slot i).1,(slot i).2,congrArg element (square_cover i hs)⟩
  · intro c a b hab
    apply congrArg element
    apply commuting_unique
    apply element_injective
    simpa only [element_multiply] using hab

private theorem test_kernel (a b : Fin 5) (v : Coordinates)
    (hf : ∀ k : Fin 3, action (element (actor (actors a b k))).val.val v = v)
    (hz : ∀ j : Fin 4, v (free a b j) = 0) : v = 0 := by
  have hd (k : Fin 3) : disp (actors a b k) *ᵥ v = 0 := by
    rw [←native_disp,displacementMatrix_eq,LinearMap.toMatrix'_mulVec]
    exact sub_eq_zero.mpr (hf k)
  have ht : test a b *ᵥ v = 0 := by
    ext i
    by_cases hi : i.val < 6
    · let n := select a b ⟨i.val,hi⟩
      simpa only [Matrix.mulVec, test, dif_pos hi, n, Pi.zero_apply] using
        congrFun (hd ⟨n.val / 10,by omega⟩) ⟨n.val % 10,by omega⟩
    · simpa [test,hi,Matrix.mulVec,dotProduct] using hz ⟨i.val-6,by omega⟩
  have hx := congrArg (fun M => M *ᵥ v) (inverse_certificate a b)
  rw [←Matrix.mulVec_mulVec,ht,Matrix.mulVec_zero,Matrix.one_mulVec] at hx
  exact hx.symm

/-- Every elementary eight in the native M12 Sylow fixes at most four heart coordinates. -/
theorem sylow_eight_fixed (E : Subgroup sylowCandidate)
    (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 8) :
    Module.finrank (ZMod 2)
      (fixedSpace (coordinateRepresentation.comp sylowCandidate.subtype) E) ≤ 4 := by
  obtain ⟨a,ha⟩ := sylow_hits_bucket E hE hcard 2
  obtain ⟨b,hb⟩ := sylow_hits_bucket E hE hcard 4
  obtain ⟨c,hc⟩ := sylow_hits_bucket E hE hcard 1
  have hz : element 4 ∈ E := by
    have hh : bucket 1 c = 4 := by fin_cases c <;> rfl
    rwa [hh] at hc
  have hactors (k : Fin 3) : element (actor (actors a b k)) ∈ E := by
    fin_cases k
    · exact hz
    · have he : actor (actors a b 1) = bucket 2 a := by fin_cases a <;> rfl
      exact he.symm ▸ ha
    · have he : actor (actors a b 2) = bucket 4 b := by fin_cases b <;> rfl
      exact he.symm ▸ hb
  let P : fixedSpace (coordinateRepresentation.comp sylowCandidate.subtype) E →ₗ[ZMod 2]
      (Fin 4 → ZMod 2) :=
    { toFun := fun v j => v.val (free a b j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hi : Function.Injective P := by
    apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro v hv
    change v = 0
    apply Subtype.ext
    apply test_kernel a b v.val
    · intro k
      exact v.property ⟨_,hactors k⟩
    · intro j
      exact congrFun hv j
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using
    LinearMap.finrank_le_finrank_of_injective hi

/-- An elementary eight of the actual native M12 displaces at least six heart dimensions. -/
theorem eight_fixedCodim (E : Subgroup M12) (hE : IsElementaryTwo E)
    (hrank : rank E = 3) : 6 ≤ fixedCodim m12HeartRepresentation E := by
  obtain ⟨B,hB,hr,hc⟩ := elementary_geometry_of_sylow_range
    (coordinateRepresentation.comp sylowCandidate.subtype) m12HeartRepresentation
    sylowCandidate.subtype sylowCandidate.subtype_injective heartEquiv
    (fun g v => heartEquiv_action g.val.val v) commonSylow
    (by rw [range_subtype]; exact le_rfl) E hE
  have hcard : Nat.card B = 8 := by
    let := hB.2
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
    have he : n = 3 := by simpa only [rank,hn,Nat.log_pow Nat.one_lt_two] using hr.trans hrank
    simp only [hn,he]; rfl
  have hfix := sylow_eight_fixed B hB.2 hcard
  have hdim := fixedCodim_add_finrank (coordinateRepresentation.comp sylowCandidate.subtype) B
  rw [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,hc] at hdim
  omega

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM12Eight
