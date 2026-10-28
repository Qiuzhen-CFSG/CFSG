module

public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalImageBound.PairCandidates
/-!
# Certificates for exhaustion of the Sylow generator images

The kernel checks four relations of `s3` and `s8`, the possible involutions
outside the characteristic centralizer, and the first-image sieve with `s8`
fixed. The 64 second candidates are conjugate to `s8`; conjugation by both
Sylow generators preserves the 128 first candidates. These smaller checks
replace a test of all pairs. Equality of Sylow elements is recovered from
the already certified separating points 0 and 930 in the assembly module.

Source: Parrott (1972), §5, p.683, with the actual Atlas1600 marking. The
auxiliary word relation and conjugators are verified in that model, not
assumed from GAP. See `source/generate_certificate.py` for the witness data.
-/

@[expose] public section
namespace Tits.SharpOuterBound.LocalImageBound.SylowPairExhaustion.Certificate
open OuterOddSubgroups.OverlapCentralizers
open Atlas1600SylowTwoCertificate

def fastForm (n : Fin 2048) : Equiv.Perm (Fin 1600) :=
  Packed.perm 2 ^ (n.val % 2) * Packed.perm 3 ^ (n.val / 2 % 2) *
  Packed.perm 4 ^ (n.val / 4 % 4) * Packed.perm 5 ^ (n.val / 16 % 2) *
  Packed.perm 6 ^ (n.val / 32 % 4) * Packed.perm 7 ^ (n.val / 128 % 2) *
  Packed.perm 8 ^ (n.val / 256 % 4) * Packed.perm 9 ^ (n.val / 1024 % 2)

theorem fastForm_eq (n : Fin 2048) : fastForm n = normalForm n := by
  simp [fastForm, Packed.perm_eq, Packed.generator, normalForm]

def leftWord {G : Type*} [Monoid G] (x y : G) : G :=
  x * y * x ^ 3 * y * x ^ 2 * y * x * y

def rightWord {G : Type*} [Monoid G] (x y : G) : G :=
  y * x ^ 3 * y * x ^ 2 * y * x * y * x

def firstDecodeData : Nat := 6020450201347548583348907279562008722353254968056543952028382541917916843038476983321843470236913862164810936742480502747830813104360701966603792242463438109485773277832240505539094187722495795378877633903679363719079491367571803242131775813883041567833373110056412319241677031716040873583254547887068351484564408491647362571547464731382752421713282941170763128827039793875696290111852694651330232991773610273677285730248257053210455870068069919957300634437311176289182702607372005127054508807674382850604729812660571889104382578878703398425839564354578409090825819169682563272532228514430056713036513428161036644333395600531363792635909299843610795093369755266159051787019529599850328547930797039126145578752085354081060695160235382722441476295645645877846336691786446169225636411754158878109341454835649009604823356891507836519183827301221398956364840850476260173518497206264078254285363007754980345009721337777891889398588304996042033677881284826368445297312266833247709929243080341873072357537862220398011955406413410809941582363461585943196385978434570617178126879233886303674243049068899913817742819618165179002915795939732733459237474813134885573895574974411256459294400610377812535657374798145320610018217149792716374387691674562274320090457332413164138216937930810615615475647624574336084601521355265528327326896236815079194853564665403147408891569107453743515516411412764653647203374675353623280892021333191743633478591484958793732938341297875318634093988181304954687751466510658350632739381003177519094865240617422999885945178309665096464886729657754352396858991472833255147952209163310248398224206141857424795352936384238848011101243392391358559296249753976852058825229073461377563630609701052496850112403965035988997013360469596367073448174525180752737366311697957668850280485065482304897536895372648229382283841694499968935333585152006320209352005940043724057259223339659203561803669691286624109714867040371874877784523864470896560530468931175054127742151648062619740865993567975692609857675171856921493199641834917938406678408634234356343318323571032653458217166061528257179339866414184000861836078165697381366022141448727783846090092253806592

def firstDecode (n : Fin 2048) : Fin 128 :=
  ⟨(firstDecodeData >>> (7 * n.val)) % 128, Nat.mod_lt _ (by decide)⟩

def secondDecode (n : Fin 2048) : Fin 64 :=
  ⟨n.val / 16 % 64, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 20000 in
theorem marked_relations :
    Packed.perm 4 ^ 4 = 1 ∧ Packed.perm 9 ^ 2 = 1 ∧
    (Packed.perm 4 * Packed.perm 9) ^ 8 = fastForm 65 ∧
    leftWord (Packed.perm 4) (Packed.perm 9) =
      rightWord (Packed.perm 4) (Packed.perm 9) := by
  have h : ∀ p : Fin 1600,
      (Packed.perm 4 ^ 4) p = p ∧ (Packed.perm 9 ^ 2) p = p ∧
      ((Packed.perm 4 * Packed.perm 9) ^ 8) p = fastForm 65 p ∧
      leftWord (Packed.perm 4) (Packed.perm 9) p =
        rightWord (Packed.perm 4) (Packed.perm 9) p := by
    apply Atlas1600OrderCertificate.allFin
    decide +kernel
  exact ⟨Equiv.ext (fun p => (h p).1), Equiv.ext (fun p => (h p).2.1),
    Equiv.ext (fun p => (h p).2.2.1), Equiv.ext (fun p => (h p).2.2.2)⟩
set_option maxRecDepth 20000 in
theorem second_candidates (n : Fin 2048) :
    n.val < 1024 ∨ (fastForm n ^ 2) 0 ≠ 0 ∨ secondIndices (secondDecode n) = n := by
  revert n
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 20000 in
theorem first_fixed_candidates (n : Fin 2048) :
    firstIndices (firstDecode n) = n ∨ (fastForm n ^ 4) 0 ≠ 0 ∨
      ((fastForm n * Packed.perm 9) ^ 8) 0 ≠ (fastForm 65) 0 ∨
      leftWord (fastForm n) (Packed.perm 9) 0 ≠
        rightWord (fastForm n) (Packed.perm 9) 0 := by
  revert n
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

def secondConjugator : Fin 64 → Fin 2048 :=
  ![0, 37, 291, 263, 11, 46, 296, 268, 44, 2, 261, 298, 39, 9, 270, 289, 257, 303, 42, 14, 266, 292, 33, 5, 294, 259, 7, 40, 301, 264, 12, 35, 47, 10, 260, 299, 36, 1, 271, 288, 8, 38, 290, 262, 3, 45, 297, 269, 295, 258, 15, 43, 300, 265, 4, 32, 256, 302, 41, 6, 267, 293, 34, 13]

def firstConjugate : Fin 2 → Fin 128 → Fin 128 :=
  ![![0, 1, 2, 3, 7, 6, 5, 4, 13, 12, 15, 14, 10, 11, 8, 9, 16, 17, 18, 19, 23, 22, 21, 20, 29, 28, 31, 30, 26, 27, 24, 25, 36, 37, 38, 39, 35, 34, 33, 32, 42, 43, 40, 41, 45, 44, 47, 46, 52, 53, 54, 55, 51, 50, 49, 48, 58, 59, 56, 57, 61, 60, 63, 62, 125, 124, 127, 126, 121, 120, 123, 122, 103, 102, 101, 100, 99, 98, 97, 96, 109, 108, 111, 110, 105, 104, 107, 106, 119, 118, 117, 116, 115, 114, 113, 112, 74, 75, 72, 73, 78, 79, 76, 77, 83, 82, 81, 80, 87, 86, 85, 84, 90, 91, 88, 89, 94, 95, 92, 93, 67, 66, 65, 64, 71, 70, 69, 68],
    ![90, 108, 127, 73, 78, 120, 107, 93, 69, 96, 115, 86, 65, 100, 119, 82, 74, 124, 111, 89, 94, 104, 123, 77, 85, 112, 99, 70, 81, 116, 103, 66, 109, 91, 72, 126, 121, 79, 92, 106, 113, 84, 71, 98, 117, 80, 67, 102, 125, 75, 88, 110, 105, 95, 76, 122, 97, 68, 87, 114, 101, 64, 83, 118, 61, 12, 31, 46, 57, 8, 27, 42, 34, 3, 16, 49, 54, 23, 4, 37, 45, 28, 15, 62, 41, 24, 11, 58, 50, 19, 0, 33, 38, 7, 20, 53, 9, 56, 43, 26, 13, 60, 47, 30, 21, 52, 39, 6, 1, 32, 51, 18, 25, 40, 59, 10, 29, 44, 63, 14, 5, 36, 55, 22, 17, 48, 35, 2]]

def conjugatingGenerator : Fin 2 → Equiv.Perm (Fin 1600) :=
  ![Packed.perm 4, Packed.perm 9]

set_option maxRecDepth 20000 in
theorem second_conjugates (j : Fin 64) :
    let c := fastForm (secondConjugator j)
    (c * fastForm (secondIndices j)) 0 = (Packed.perm 9 * c) 0 ∧
    (c * fastForm (secondIndices j)) 930 = (Packed.perm 9 * c) 930 := by
  revert j
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 20000 in
theorem first_conjugates (g : Fin 2) (i : Fin 128) :
    let a := conjugatingGenerator g
    let x := fastForm (firstIndices i)
    let y := fastForm (firstIndices (firstConjugate g i))
    (a * x) 0 = (y * a) 0 ∧ (a * x) 930 = (y * a) 930 := by
  revert g i
  apply Atlas1600OrderCertificate.allFin₂
  decide +kernel
end Tits.SharpOuterBound.LocalImageBound.SylowPairExhaustion.Certificate
end
