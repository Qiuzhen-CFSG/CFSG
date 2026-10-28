module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.Transport
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.SimpleConjugation


/-!
# Exact root transport for nonzero F4 rank-one words

Every word `x_r(t) x_{-r}(-t⁻¹) x_r(t)`, with `t` a unit in the Ree coefficient
field, conjugates all root curves by a root permutation and unit parameter
scalars. All conjugations here act on the left.

The simple parameter-one word is the integral Tits lift, whose all-root action
is proved in `SimpleConjugation`. For a general parameter, choose a square root
of `t` in the finite characteristic-two field. Its simple-coroot diagonal
matrix scales the positive simple curve by `t` and the negative simple curve
by `t⁻¹`, so it carries the parameter-one rank-one word to the required word.
The canonical Tits routes then handle every positive root and its negative.
We compose these concrete matrix actions and finally restrict the resulting
identity to the split group; the auxiliary diagonal matrices need no assumed
membership in that group.

Source: GLS3 1.12.1(g,h) and 2.3.8(b), in
`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/chapter2.tex`.
The proof applies also to the binary case `m = 0`.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction ReeF4.WordRelations
open scoped Matrix
noncomputable section
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
namespace NormalizerGeometry.RankOneTransport

private abbrev MatrixUnit (S : Type*) [CommRing S] :=
  (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex S)ˣ

private structure MatrixTransport {S : Type*} [CommRing S] (n : MatrixUnit S) where
  perm : Equiv.Perm F4Chevalley.Root
  scale : F4Chevalley.Root → Sˣ
  conj_root : ∀ r t, n * F4Chevalley.rootCurve r t * n⁻¹ =
    F4Chevalley.rootCurve (perm r) ((scale r : S) * t)

private def MatrixTransport.one {S : Type*} [CommRing S] :
    MatrixTransport (1 : MatrixUnit S) where
  perm := Equiv.refl _
  scale := fun _ => 1
  conj_root := by intros; simp

private def MatrixTransport.mul {S : Type*} [CommRing S] {n k : MatrixUnit S}
    (a : MatrixTransport n) (b : MatrixTransport k) : MatrixTransport (n * k) where
  perm := a.perm * b.perm
  scale := fun r => a.scale (b.perm r) * b.scale r
  conj_root := by
    intro r t
    calc
      _ = n * (k * F4Chevalley.rootCurve r t * k⁻¹) * n⁻¹ := by group
      _ = _ := by rw [b.conj_root, a.conj_root]; simp [Equiv.Perm.mul_apply, mul_assoc]

private def MatrixTransport.inv {S : Type*} [CommRing S] {n : MatrixUnit S}
    (a : MatrixTransport n) : MatrixTransport n⁻¹ where
  perm := a.perm.symm
  scale := fun r => (a.scale (a.perm.symm r))⁻¹
  conj_root := by
    intro r t
    have he : n * F4Chevalley.rootCurve (a.perm.symm r)
        (((a.scale (a.perm.symm r))⁻¹ : Sˣ) * t) * n⁻¹ =
        F4Chevalley.rootCurve r t := by
      rw [a.conj_root, a.perm.apply_symm_apply]
      simp
    rw [inv_inv, ← he]
    group

private def MatrixTransport.conjugate {S : Type*} [CommRing S] {n k : MatrixUnit S}
    (a : MatrixTransport n) (b : MatrixTransport k) : MatrixTransport (n * k * n⁻¹) :=
  (a.mul b).mul a.inv

private def MatrixTransport.simple {S : Type*} [CommRing S] [CharP S 2]
    (i : typeF4RootPairing_base.support) : MatrixTransport (titsUnit (S := S) [i]) where
  perm := typeF4RootPairing.reflectionPerm i
  scale := fun _ => 1
  conj_root := by intro r t; simpa using simple_conj i r t

private def MatrixTransport.word {S : Type*} [CommRing S] [CharP S 2]
    (w : List typeF4RootPairing_base.support) : MatrixTransport (titsUnit (S := S) w) := by
  induction w with
  | nil => simpa using (MatrixTransport.one (S := S))
  | cons i w ih =>
    have he : titsUnit (S := S) (i :: w) = titsUnit [i] * titsUnit w := by
      rw [titsUnit_cons, titsUnit_cons, titsUnit_nil, mul_one]
    rw [he]
    exact (MatrixTransport.simple i).mul ih

private def MatrixTransport.torus {S : Type*} [CommRing S]
    (u : IntegralChevalleyTorusParameter (b := typeF4RootPairing_base) S) :
    MatrixTransport (F4Chevalley.torusConjugation.torusElement u)⁻¹ where
  perm := Equiv.refl _
  scale := integralChevalleyRootScale (P := typeF4RootPairing) u
  conj_root := by intro r t; simpa using F4Chevalley.rootCurve_torus_conjugation u r t

private def matrixRankOne {S : Type*} [CommRing S] (r : F4Chevalley.Root) (t : Sˣ) :
    MatrixUnit S :=
  F4Chevalley.rootCurve r (t : S) * F4Chevalley.rootCurve (-r) (-((t⁻¹ : Sˣ) : S)) *
    F4Chevalley.rootCurve r (t : S)

private theorem matrixRankOne_simple_one {S : Type*} [CommRing S]
    (i : typeF4RootPairing_base.support) :
    matrixRankOne (S := S) i.val 1 = titsUnit [i] := by
  simp only [matrixRankOne, titsUnit_cons, titsUnit_nil, mul_one, inv_one, Units.val_one]

private theorem exists_unit_sqrt {K : Type*} [Field K] [CharP K 2] [Finite K] (t : Kˣ) :
    ∃ u : Kˣ, u ^ 2 = t := by
  have hinj : Function.Injective (fun u : Kˣ => u ^ 2) := by
    intro u v h
    apply Units.ext
    apply CharTwo.sq_injective
    exact congrArg Units.val h
  exact Finite.surjective_of_injective hinj t

private theorem matrixRankOne_simple {K : Type*} [Field K] [CharP K 2] [Finite K]
    (i : typeF4RootPairing_base.support) (t : Kˣ) :
    Nonempty (MatrixTransport (matrixRankOne i.val t)) := by
  obtain ⟨u, hu⟩ := exists_unit_sqrt t
  let p := integralChevalleySimpleCorootParameter (b := typeF4RootPairing_base) i u
  let d := F4Chevalley.torusConjugation.torusElement p
  have he (a : K) : d⁻¹ * F4Chevalley.rootCurve i.val a * d =
      F4Chevalley.rootCurve i.val ((t : K) * a) := by
    simpa only [RootPairing.pairingIn_same, zpow_ofNat, hu] using
      F4Chevalley.rootCurve_simpleCoroot_conjugation i u i.val a
  have hf (a : K) : d⁻¹ * F4Chevalley.rootCurve (-i.val) a * d =
      F4Chevalley.rootCurve (-i.val) (((t⁻¹ : Kˣ) : K) * a) := by
    simpa only [RootPairing.indexNeg_neg, RootPairing.pairingIn_reflectionPerm_self_left,
      RootPairing.pairingIn_same, zpow_neg, zpow_ofNat, hu] using
      F4Chevalley.rootCurve_simpleCoroot_conjugation i u (-i.val) a
  have hn : matrixRankOne i.val t = d⁻¹ * titsUnit [i] * d := by
    rw [← matrixRankOne_simple_one i]
    calc
      _ = (d⁻¹ * F4Chevalley.rootCurve i.val 1 * d) *
          (d⁻¹ * F4Chevalley.rootCurve (-i.val) (-1) * d) *
          (d⁻¹ * F4Chevalley.rootCurve i.val 1 * d) := by
        rw [he, hf]
        simp only [mul_one, mul_neg, matrixRankOne]
      _ = _ := by simp only [matrixRankOne, inv_one, Units.val_one]; group
  rw [hn]
  have h := (MatrixTransport.torus p).conjugate (MatrixTransport.simple i)
  simpa only [inv_inv] using (Nonempty.intro h)

private theorem matrixRankOne_conjugate {S : Type*} [CommRing S]
    (n : MatrixUnit S) (r s : F4Chevalley.Root)
    (hp : ∀ a, n * F4Chevalley.rootCurve r a * n⁻¹ = F4Chevalley.rootCurve s a)
    (hn : ∀ a, n * F4Chevalley.rootCurve (-r) a * n⁻¹ = F4Chevalley.rootCurve (-s) a)
    (t : Sˣ) : matrixRankOne s t = n * matrixRankOne r t * n⁻¹ := by
  dsimp only [matrixRankOne]
  rw [← hp, ← hn]
  group

private theorem matrixRankOne_neg_simple {K : Type*} [Field K] [CharP K 2] [Finite K]
    (i : typeF4RootPairing_base.support) (t : Kˣ) :
    Nonempty (MatrixTransport (matrixRankOne (-i.val) t)) := by
  have hp (a : K) : titsUnit [i] * F4Chevalley.rootCurve i.val a * (titsUnit [i])⁻¹ =
      F4Chevalley.rootCurve (-i.val) a := simple_conj i i.val a
  have hn (a : K) : titsUnit [i] * F4Chevalley.rootCurve (-i.val) a * (titsUnit [i])⁻¹ =
      F4Chevalley.rootCurve (-(-i.val)) a := by
    rw [neg_neg]
    simpa only [RootPairing.indexNeg_neg, RootPairing.reflectionPerm_self] using
      simple_conj i (-i.val) a
  rw [matrixRankOne_conjugate (titsUnit [i]) i.val (-i.val) hp hn t]
  obtain ⟨h⟩ := matrixRankOne_simple i t
  exact ⟨(MatrixTransport.simple i).conjugate h⟩

private theorem matrixRankOne_transport {K : Type*} [Field K] [CharP K 2] [Finite K]
    (r : F4Chevalley.Root) (t : Kˣ) :
    Nonempty (MatrixTransport (matrixRankOne r t)) := by
  by_cases hr : typeF4RootPairing_base.IsPos r
  · let D := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
    have hp (a : K) : titsUnit D.word * F4Chevalley.rootCurve D.simple.val a *
        (titsUnit D.word)⁻¹ = F4Chevalley.rootCurve r a :=
      (rootCurve_of_pos_route r hr a).symm
    have hn (a : K) : titsUnit D.word * F4Chevalley.rootCurve (-D.simple.val) a *
        (titsUnit D.word)⁻¹ = F4Chevalley.rootCurve (-r) a :=
      (rootCurve_neg_of_pos_route r hr a).symm
    rw [matrixRankOne_conjugate (titsUnit D.word) D.simple.val r hp hn t]
    obtain ⟨h⟩ := matrixRankOne_simple D.simple t
    exact ⟨(MatrixTransport.word D.word).conjugate h⟩
  · have hneg := (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr
    let D := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)
    have hp (a : K) : titsUnit D.word * F4Chevalley.rootCurve (-D.simple.val) a *
        (titsUnit D.word)⁻¹ = F4Chevalley.rootCurve r a := by
      simpa only [neg_neg] using (rootCurve_neg_of_pos_route (-r) hneg a).symm
    have hn (a : K) : titsUnit D.word * F4Chevalley.rootCurve (-(-D.simple.val)) a *
        (titsUnit D.word)⁻¹ = F4Chevalley.rootCurve (-r) a := by
      simpa only [neg_neg] using (rootCurve_of_pos_route (-r) hneg a).symm
    rw [matrixRankOne_conjugate (titsUnit D.word) (-D.simple.val) r hp hn t]
    obtain ⟨h⟩ := matrixRankOne_neg_simple D.simple t
    exact ⟨(MatrixTransport.word D.word).conjugate h⟩

end NormalizerGeometry.RankOneTransport

/-- Every nonzero rank-one word in the concrete split F4 group permutes all
root curves with unit parameter scales. This holds also for `m = 0`. -/
theorem rootTransport_rankOneRepresentative (m : ℕ) (r : F4Chevalley.Root)
    (t : (CoefficientField m)ˣ) :
    Nonempty (RootTransport (rankOneRepresentative m r t)) := by
  obtain ⟨h⟩ := NormalizerGeometry.RankOneTransport.matrixRankOne_transport r t
  refine ⟨{ perm := h.perm, scale := h.scale, conj_root := ?_ }⟩
  intro q a
  apply Subtype.ext
  exact h.conj_root q a

end ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
