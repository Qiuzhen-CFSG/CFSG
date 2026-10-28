module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.CachedActions
import Mathlib.Tactic.FinCases

/-!
# Prime-order obstructions for Held representatives 1792 through 2047

For every nonlocal row, kernel reduction verifies a nontrivial prime orbit
of a word in the actual marked generators and representative. The orbit
lemma then constructs an element of that prime order in their generated
subgroup. The cached marked actions are proved equal to the originals.

Source: `../source/orbits.json`, generated from the unchanged ATLAS carrier
by `../source/search_orbits.py`. Emitted by `source/generate.py`; the generator
and JSON are not trusted proof inputs.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification

set_option Elab.async false

set_option maxRecDepth 16000 in
private theorem obstruction_1792 : HasPrimeObstruction (representative 1792) := by
  apply obstruction_of_cachedAction 1792 [5, 2] 5 1
    (by decide) (by decide) (by decide) 15
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1793 : HasPrimeObstruction (representative 1793) := by
  apply obstruction_of_cachedAction 1793 [5, 1] 5 1
    (by decide) (by decide) (by decide) 202
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1794 : HasPrimeObstruction (representative 1794) := by
  apply obstruction_of_cachedAction 1794 [5] 7 1
    (by decide) (by decide) (by decide) 66
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1795 : HasPrimeObstruction (representative 1795) := by
  apply obstruction_of_cachedAction 1795 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1796 : HasPrimeObstruction (representative 1796) := by
  apply obstruction_of_cachedAction 1796 [5] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1797 : HasPrimeObstruction (representative 1797) := by
  apply obstruction_of_cachedAction 1797 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1798 : HasPrimeObstruction (representative 1798) := by
  apply obstruction_of_cachedAction 1798 [5] 7 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1799 : HasPrimeObstruction (representative 1799) := by
  apply obstruction_of_cachedAction 1799 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1800 : HasPrimeObstruction (representative 1800) := by
  apply obstruction_of_cachedAction 1800 [5, 1] 7 1
    (by decide) (by decide) (by decide) 64
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1801 : HasPrimeObstruction (representative 1801) := by
  apply obstruction_of_cachedAction 1801 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1802 : HasPrimeObstruction (representative 1802) := by
  apply obstruction_of_cachedAction 1802 [5, 1] 5 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1803 : HasPrimeObstruction (representative 1803) := by
  apply obstruction_of_cachedAction 1803 [5] 5 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1804 : HasPrimeObstruction (representative 1804) := by
  apply obstruction_of_cachedAction 1804 [5, 4] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1805 : HasPrimeObstruction (representative 1805) := by
  apply obstruction_of_cachedAction 1805 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1806 : HasPrimeObstruction (representative 1806) := by
  apply obstruction_of_cachedAction 1806 [5, 2] 5 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1807 : HasPrimeObstruction (representative 1807) := by
  apply obstruction_of_cachedAction 1807 [5] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1808 : HasPrimeObstruction (representative 1808) := by
  apply obstruction_of_cachedAction 1808 [5] 7 1
    (by decide) (by decide) (by decide) 64
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1809 : HasPrimeObstruction (representative 1809) := by
  apply obstruction_of_cachedAction 1809 [5, 2] 5 1
    (by decide) (by decide) (by decide) 58
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1810 : HasPrimeObstruction (representative 1810) := by
  apply obstruction_of_cachedAction 1810 [5, 1] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1811 : HasPrimeObstruction (representative 1811) := by
  apply obstruction_of_cachedAction 1811 [5, 1] 5 1
    (by decide) (by decide) (by decide) 20
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1812 : HasPrimeObstruction (representative 1812) := by
  apply obstruction_of_cachedAction 1812 [5] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1813 : HasPrimeObstruction (representative 1813) := by
  apply obstruction_of_cachedAction 1813 [5] 5 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1814 : HasPrimeObstruction (representative 1814) := by
  apply obstruction_of_cachedAction 1814 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1815 : HasPrimeObstruction (representative 1815) := by
  apply obstruction_of_cachedAction 1815 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1816 : HasPrimeObstruction (representative 1816) := by
  apply obstruction_of_cachedAction 1816 [5, 1] 7 1
    (by decide) (by decide) (by decide) 25
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1817 : HasPrimeObstruction (representative 1817) := by
  apply obstruction_of_cachedAction 1817 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1818 : HasPrimeObstruction (representative 1818) := by
  apply obstruction_of_cachedAction 1818 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1819 : HasPrimeObstruction (representative 1819) := by
  apply obstruction_of_cachedAction 1819 [5] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1820 : HasPrimeObstruction (representative 1820) := by
  apply obstruction_of_cachedAction 1820 [5] 7 1
    (by decide) (by decide) (by decide) 60
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1821 : HasPrimeObstruction (representative 1821) := by
  apply obstruction_of_cachedAction 1821 [5] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1822 : HasPrimeObstruction (representative 1822) := by
  apply obstruction_of_cachedAction 1822 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1823 : HasPrimeObstruction (representative 1823) := by
  apply obstruction_of_cachedAction 1823 [5, 2] 5 1
    (by decide) (by decide) (by decide) 68
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1824 : HasPrimeObstruction (representative 1824) := by
  apply obstruction_of_cachedAction 1824 [5, 4] 7 1
    (by decide) (by decide) (by decide) 41
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1825 : HasPrimeObstruction (representative 1825) := by
  apply obstruction_of_cachedAction 1825 [5, 2] 7 1
    (by decide) (by decide) (by decide) 61
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1826 : HasPrimeObstruction (representative 1826) := by
  apply obstruction_of_cachedAction 1826 [5] 7 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1827 : HasPrimeObstruction (representative 1827) := by
  apply obstruction_of_cachedAction 1827 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1828 : HasPrimeObstruction (representative 1828) := by
  apply obstruction_of_cachedAction 1828 [5] 5 1
    (by decide) (by decide) (by decide) 45
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1829 : HasPrimeObstruction (representative 1829) := by
  apply obstruction_of_cachedAction 1829 [5, 2] 5 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1830 : HasPrimeObstruction (representative 1830) := by
  apply obstruction_of_cachedAction 1830 [5] 7 1
    (by decide) (by decide) (by decide) 43
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1831 : HasPrimeObstruction (representative 1831) := by
  apply obstruction_of_cachedAction 1831 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1832 : HasPrimeObstruction (representative 1832) := by
  apply obstruction_of_cachedAction 1832 [5] 7 1
    (by decide) (by decide) (by decide) 38
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1833 : HasPrimeObstruction (representative 1833) := by
  apply obstruction_of_cachedAction 1833 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1834 : HasPrimeObstruction (representative 1834) := by
  apply obstruction_of_cachedAction 1834 [5] 7 1
    (by decide) (by decide) (by decide) 87
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1835 : HasPrimeObstruction (representative 1835) := by
  apply obstruction_of_cachedAction 1835 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1836 : HasPrimeObstruction (representative 1836) := by
  apply obstruction_of_cachedAction 1836 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1837 : HasPrimeObstruction (representative 1837) := by
  apply obstruction_of_cachedAction 1837 [5] 7 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1838 : HasPrimeObstruction (representative 1838) := by
  apply obstruction_of_cachedAction 1838 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1839 : HasPrimeObstruction (representative 1839) := by
  apply obstruction_of_cachedAction 1839 [5] 7 1
    (by decide) (by decide) (by decide) 23
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1840 : HasPrimeObstruction (representative 1840) := by
  apply obstruction_of_cachedAction 1840 [5, 1] 7 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1841 : HasPrimeObstruction (representative 1841) := by
  apply obstruction_of_cachedAction 1841 [5] 7 1
    (by decide) (by decide) (by decide) 69
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1842 : HasPrimeObstruction (representative 1842) := by
  apply obstruction_of_cachedAction 1842 [5] 7 1
    (by decide) (by decide) (by decide) 23
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1843 : HasPrimeObstruction (representative 1843) := by
  apply obstruction_of_cachedAction 1843 [5] 7 1
    (by decide) (by decide) (by decide) 24
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1844 : HasPrimeObstruction (representative 1844) := by
  apply obstruction_of_cachedAction 1844 [5] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1845 : HasPrimeObstruction (representative 1845) := by
  apply obstruction_of_cachedAction 1845 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1846 : HasPrimeObstruction (representative 1846) := by
  apply obstruction_of_cachedAction 1846 [5] 7 1
    (by decide) (by decide) (by decide) 81
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1847 : HasPrimeObstruction (representative 1847) := by
  apply obstruction_of_cachedAction 1847 [5, 1] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1848 : HasPrimeObstruction (representative 1848) := by
  apply obstruction_of_cachedAction 1848 [5] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1849 : HasPrimeObstruction (representative 1849) := by
  apply obstruction_of_cachedAction 1849 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1850 : HasPrimeObstruction (representative 1850) := by
  apply obstruction_of_cachedAction 1850 [5, 1] 5 1
    (by decide) (by decide) (by decide) 32
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1851 : HasPrimeObstruction (representative 1851) := by
  apply obstruction_of_cachedAction 1851 [5] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1852 : HasPrimeObstruction (representative 1852) := by
  apply obstruction_of_cachedAction 1852 [5] 7 1
    (by decide) (by decide) (by decide) 138
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1853 : HasPrimeObstruction (representative 1853) := by
  apply obstruction_of_cachedAction 1853 [5, 1] 7 1
    (by decide) (by decide) (by decide) 144
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1854 : HasPrimeObstruction (representative 1854) := by
  apply obstruction_of_cachedAction 1854 [5] 7 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1855 : HasPrimeObstruction (representative 1855) := by
  apply obstruction_of_cachedAction 1855 [5, 3] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1856 : HasPrimeObstruction (representative 1856) := by
  apply obstruction_of_cachedAction 1856 [5, 3] 7 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1857 : HasPrimeObstruction (representative 1857) := by
  apply obstruction_of_cachedAction 1857 [5, 2] 7 1
    (by decide) (by decide) (by decide) 50
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1858 : HasPrimeObstruction (representative 1858) := by
  apply obstruction_of_cachedAction 1858 [5] 5 1
    (by decide) (by decide) (by decide) 33
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1859 : HasPrimeObstruction (representative 1859) := by
  apply obstruction_of_cachedAction 1859 [5, 4] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1860 : HasPrimeObstruction (representative 1860) := by
  apply obstruction_of_cachedAction 1860 [5, 2] 7 1
    (by decide) (by decide) (by decide) 198
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1861 : HasPrimeObstruction (representative 1861) := by
  apply obstruction_of_cachedAction 1861 [5] 7 1
    (by decide) (by decide) (by decide) 87
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1862 : HasPrimeObstruction (representative 1862) := by
  apply obstruction_of_cachedAction 1862 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1863 : HasPrimeObstruction (representative 1863) := by
  apply obstruction_of_cachedAction 1863 [5, 3] 5 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1864 : HasPrimeObstruction (representative 1864) := by
  apply obstruction_of_cachedAction 1864 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1865 : HasPrimeObstruction (representative 1865) := by
  apply obstruction_of_cachedAction 1865 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1866 : HasPrimeObstruction (representative 1866) := by
  apply obstruction_of_cachedAction 1866 [5] 7 1
    (by decide) (by decide) (by decide) 107
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1867 : HasPrimeObstruction (representative 1867) := by
  apply obstruction_of_cachedAction 1867 [5] 7 1
    (by decide) (by decide) (by decide) 62
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1868 : HasPrimeObstruction (representative 1868) := by
  apply obstruction_of_cachedAction 1868 [5] 5 1
    (by decide) (by decide) (by decide) 62
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1869 : HasPrimeObstruction (representative 1869) := by
  apply obstruction_of_cachedAction 1869 [5, 2] 5 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1870 : HasPrimeObstruction (representative 1870) := by
  apply obstruction_of_cachedAction 1870 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1871 : HasPrimeObstruction (representative 1871) := by
  apply obstruction_of_cachedAction 1871 [5, 2] 7 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1872 : HasPrimeObstruction (representative 1872) := by
  apply obstruction_of_cachedAction 1872 [5] 7 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1873 : HasPrimeObstruction (representative 1873) := by
  apply obstruction_of_cachedAction 1873 [5, 1] 5 1
    (by decide) (by decide) (by decide) 37
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1874 : HasPrimeObstruction (representative 1874) := by
  apply obstruction_of_cachedAction 1874 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1875 : HasPrimeObstruction (representative 1875) := by
  apply obstruction_of_cachedAction 1875 [5] 5 1
    (by decide) (by decide) (by decide) 86
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1876 : HasPrimeObstruction (representative 1876) := by
  apply obstruction_of_cachedAction 1876 [5] 7 1
    (by decide) (by decide) (by decide) 33
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1877 : HasPrimeObstruction (representative 1877) := by
  apply obstruction_of_cachedAction 1877 [5] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1878 : HasPrimeObstruction (representative 1878) := by
  apply obstruction_of_cachedAction 1878 [5] 5 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1879 : HasPrimeObstruction (representative 1879) := by
  apply obstruction_of_cachedAction 1879 [5, 2] 5 1
    (by decide) (by decide) (by decide) 114
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1880 : HasPrimeObstruction (representative 1880) := by
  apply obstruction_of_cachedAction 1880 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1881 : HasPrimeObstruction (representative 1881) := by
  apply obstruction_of_cachedAction 1881 [5] 5 1
    (by decide) (by decide) (by decide) 87
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1882 : HasPrimeObstruction (representative 1882) := by
  apply obstruction_of_cachedAction 1882 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1883 : HasPrimeObstruction (representative 1883) := by
  apply obstruction_of_cachedAction 1883 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1884 : HasPrimeObstruction (representative 1884) := by
  apply obstruction_of_cachedAction 1884 [5, 4] 7 1
    (by decide) (by decide) (by decide) 72
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1885 : HasPrimeObstruction (representative 1885) := by
  apply obstruction_of_cachedAction 1885 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1886 : HasPrimeObstruction (representative 1886) := by
  apply obstruction_of_cachedAction 1886 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1887 : HasPrimeObstruction (representative 1887) := by
  apply obstruction_of_cachedAction 1887 [5, 2] 5 1
    (by decide) (by decide) (by decide) 15
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1888 : HasPrimeObstruction (representative 1888) := by
  apply obstruction_of_cachedAction 1888 [5, 4] 7 1
    (by decide) (by decide) (by decide) 64
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1889 : HasPrimeObstruction (representative 1889) := by
  apply obstruction_of_cachedAction 1889 [5] 5 1
    (by decide) (by decide) (by decide) 60
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1890 : HasPrimeObstruction (representative 1890) := by
  apply obstruction_of_cachedAction 1890 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1891 : HasPrimeObstruction (representative 1891) := by
  apply obstruction_of_cachedAction 1891 [5, 3] 5 1
    (by decide) (by decide) (by decide) 36
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1892 : HasPrimeObstruction (representative 1892) := by
  apply obstruction_of_cachedAction 1892 [5, 3] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1893 : HasPrimeObstruction (representative 1893) := by
  apply obstruction_of_cachedAction 1893 [5, 2] 5 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1894 : HasPrimeObstruction (representative 1894) := by
  apply obstruction_of_cachedAction 1894 [5] 7 1
    (by decide) (by decide) (by decide) 133
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1895 : HasPrimeObstruction (representative 1895) := by
  apply obstruction_of_cachedAction 1895 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1896 : HasPrimeObstruction (representative 1896) := by
  apply obstruction_of_cachedAction 1896 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1897 : HasPrimeObstruction (representative 1897) := by
  apply obstruction_of_cachedAction 1897 [5] 7 1
    (by decide) (by decide) (by decide) 24
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1898 : HasPrimeObstruction (representative 1898) := by
  apply obstruction_of_cachedAction 1898 [5, 3] 5 1
    (by decide) (by decide) (by decide) 57
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1899 : HasPrimeObstruction (representative 1899) := by
  apply obstruction_of_cachedAction 1899 [5] 7 1
    (by decide) (by decide) (by decide) 107
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1900 : HasPrimeObstruction (representative 1900) := by
  apply obstruction_of_cachedAction 1900 [5, 4] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1901 : HasPrimeObstruction (representative 1901) := by
  apply obstruction_of_cachedAction 1901 [5] 7 1
    (by decide) (by decide) (by decide) 61
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1902 : HasPrimeObstruction (representative 1902) := by
  apply obstruction_of_cachedAction 1902 [5, 2] 7 1
    (by decide) (by decide) (by decide) 21
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1903 : HasPrimeObstruction (representative 1903) := by
  apply obstruction_of_cachedAction 1903 [5] 7 1
    (by decide) (by decide) (by decide) 169
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1904 : HasPrimeObstruction (representative 1904) := by
  apply obstruction_of_cachedAction 1904 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1905 : HasPrimeObstruction (representative 1905) := by
  apply obstruction_of_cachedAction 1905 [5, 2] 7 1
    (by decide) (by decide) (by decide) 295
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1906 : HasPrimeObstruction (representative 1906) := by
  apply obstruction_of_cachedAction 1906 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1907 : HasPrimeObstruction (representative 1907) := by
  apply obstruction_of_cachedAction 1907 [5, 1] 7 1
    (by decide) (by decide) (by decide) 104
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1908 : HasPrimeObstruction (representative 1908) := by
  apply obstruction_of_cachedAction 1908 [5] 7 1
    (by decide) (by decide) (by decide) 144
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1909 : HasPrimeObstruction (representative 1909) := by
  apply obstruction_of_cachedAction 1909 [5] 7 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1910 : HasPrimeObstruction (representative 1910) := by
  apply obstruction_of_cachedAction 1910 [5, 1] 5 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1911 : HasPrimeObstruction (representative 1911) := by
  apply obstruction_of_cachedAction 1911 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1912 : HasPrimeObstruction (representative 1912) := by
  apply obstruction_of_cachedAction 1912 [5, 3] 5 1
    (by decide) (by decide) (by decide) 25
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1913 : HasPrimeObstruction (representative 1913) := by
  apply obstruction_of_cachedAction 1913 [5] 7 1
    (by decide) (by decide) (by decide) 65
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1914 : HasPrimeObstruction (representative 1914) := by
  apply obstruction_of_cachedAction 1914 [5] 7 1
    (by decide) (by decide) (by decide) 71
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1915 : HasPrimeObstruction (representative 1915) := by
  apply obstruction_of_cachedAction 1915 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1916 : HasPrimeObstruction (representative 1916) := by
  apply obstruction_of_cachedAction 1916 [5] 7 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1917 : HasPrimeObstruction (representative 1917) := by
  apply obstruction_of_cachedAction 1917 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1918 : HasPrimeObstruction (representative 1918) := by
  apply obstruction_of_cachedAction 1918 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1919 : HasPrimeObstruction (representative 1919) := by
  apply obstruction_of_cachedAction 1919 [5] 7 1
    (by decide) (by decide) (by decide) 406
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1920 : HasPrimeObstruction (representative 1920) := by
  apply obstruction_of_cachedAction 1920 [5] 7 1
    (by decide) (by decide) (by decide) 25
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1921 : HasPrimeObstruction (representative 1921) := by
  apply obstruction_of_cachedAction 1921 [5] 7 1
    (by decide) (by decide) (by decide) 160
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1922 : HasPrimeObstruction (representative 1922) := by
  apply obstruction_of_cachedAction 1922 [5, 1] 5 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1923 : HasPrimeObstruction (representative 1923) := by
  apply obstruction_of_cachedAction 1923 [5] 7 1
    (by decide) (by decide) (by decide) 169
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1924 : HasPrimeObstruction (representative 1924) := by
  apply obstruction_of_cachedAction 1924 [5, 4] 5 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1925 : HasPrimeObstruction (representative 1925) := by
  apply obstruction_of_cachedAction 1925 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1926 : HasPrimeObstruction (representative 1926) := by
  apply obstruction_of_cachedAction 1926 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1927 : HasPrimeObstruction (representative 1927) := by
  apply obstruction_of_cachedAction 1927 [5] 7 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1928 : HasPrimeObstruction (representative 1928) := by
  apply obstruction_of_cachedAction 1928 [5] 7 1
    (by decide) (by decide) (by decide) 187
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1929 : HasPrimeObstruction (representative 1929) := by
  apply obstruction_of_cachedAction 1929 [5] 7 1
    (by decide) (by decide) (by decide) 23
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1930 : HasPrimeObstruction (representative 1930) := by
  apply obstruction_of_cachedAction 1930 [5, 2] 5 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1931 : HasPrimeObstruction (representative 1931) := by
  apply obstruction_of_cachedAction 1931 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1932 : HasPrimeObstruction (representative 1932) := by
  apply obstruction_of_cachedAction 1932 [5] 5 1
    (by decide) (by decide) (by decide) 28
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1933 : HasPrimeObstruction (representative 1933) := by
  apply obstruction_of_cachedAction 1933 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1934 : HasPrimeObstruction (representative 1934) := by
  apply obstruction_of_cachedAction 1934 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1935 : HasPrimeObstruction (representative 1935) := by
  apply obstruction_of_cachedAction 1935 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1936 : HasPrimeObstruction (representative 1936) := by
  apply obstruction_of_cachedAction 1936 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1937 : HasPrimeObstruction (representative 1937) := by
  apply obstruction_of_cachedAction 1937 [5] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1938 : HasPrimeObstruction (representative 1938) := by
  apply obstruction_of_cachedAction 1938 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1939 : HasPrimeObstruction (representative 1939) := by
  apply obstruction_of_cachedAction 1939 [5] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1940 : HasPrimeObstruction (representative 1940) := by
  apply obstruction_of_cachedAction 1940 [5] 7 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1941 : HasPrimeObstruction (representative 1941) := by
  apply obstruction_of_cachedAction 1941 [5, 3] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1942 : HasPrimeObstruction (representative 1942) := by
  apply obstruction_of_cachedAction 1942 [5, 1] 5 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1943 : HasPrimeObstruction (representative 1943) := by
  apply obstruction_of_cachedAction 1943 [5, 3] 7 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1944 : HasPrimeObstruction (representative 1944) := by
  apply obstruction_of_cachedAction 1944 [5, 2] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1945 : HasPrimeObstruction (representative 1945) := by
  apply obstruction_of_cachedAction 1945 [5] 7 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1946 : HasPrimeObstruction (representative 1946) := by
  apply obstruction_of_cachedAction 1946 [5, 1] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1947 : HasPrimeObstruction (representative 1947) := by
  apply obstruction_of_cachedAction 1947 [5, 2] 5 1
    (by decide) (by decide) (by decide) 59
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1948 : HasPrimeObstruction (representative 1948) := by
  apply obstruction_of_cachedAction 1948 [5, 2] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1949 : HasPrimeObstruction (representative 1949) := by
  apply obstruction_of_cachedAction 1949 [5] 7 1
    (by decide) (by decide) (by decide) 33
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1950 : HasPrimeObstruction (representative 1950) := by
  apply obstruction_of_cachedAction 1950 [5, 4] 5 1
    (by decide) (by decide) (by decide) 99
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1951 : HasPrimeObstruction (representative 1951) := by
  apply obstruction_of_cachedAction 1951 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1952 : HasPrimeObstruction (representative 1952) := by
  apply obstruction_of_cachedAction 1952 [5] 7 1
    (by decide) (by decide) (by decide) 29
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1953 : HasPrimeObstruction (representative 1953) := by
  apply obstruction_of_cachedAction 1953 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1954 : HasPrimeObstruction (representative 1954) := by
  apply obstruction_of_cachedAction 1954 [5] 5 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1955 : HasPrimeObstruction (representative 1955) := by
  apply obstruction_of_cachedAction 1955 [5] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1956 : HasPrimeObstruction (representative 1956) := by
  apply obstruction_of_cachedAction 1956 [5] 7 1
    (by decide) (by decide) (by decide) 106
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1957 : HasPrimeObstruction (representative 1957) := by
  apply obstruction_of_cachedAction 1957 [5] 7 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1958 : HasPrimeObstruction (representative 1958) := by
  apply obstruction_of_cachedAction 1958 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1959 : HasPrimeObstruction (representative 1959) := by
  apply obstruction_of_cachedAction 1959 [5] 7 1
    (by decide) (by decide) (by decide) 33
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1960 : HasPrimeObstruction (representative 1960) := by
  apply obstruction_of_cachedAction 1960 [5, 1] 5 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1961 : HasPrimeObstruction (representative 1961) := by
  apply obstruction_of_cachedAction 1961 [5] 7 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1962 : HasPrimeObstruction (representative 1962) := by
  apply obstruction_of_cachedAction 1962 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1963 : HasPrimeObstruction (representative 1963) := by
  apply obstruction_of_cachedAction 1963 [5, 1] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1964 : HasPrimeObstruction (representative 1964) := by
  apply obstruction_of_cachedAction 1964 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1965 : HasPrimeObstruction (representative 1965) := by
  apply obstruction_of_cachedAction 1965 [5] 7 1
    (by decide) (by decide) (by decide) 159
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1966 : HasPrimeObstruction (representative 1966) := by
  apply obstruction_of_cachedAction 1966 [5] 7 1
    (by decide) (by decide) (by decide) 24
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1967 : HasPrimeObstruction (representative 1967) := by
  apply obstruction_of_cachedAction 1967 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1968 : HasPrimeObstruction (representative 1968) := by
  apply obstruction_of_cachedAction 1968 [5] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1969 : HasPrimeObstruction (representative 1969) := by
  apply obstruction_of_cachedAction 1969 [5, 1] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1970 : HasPrimeObstruction (representative 1970) := by
  apply obstruction_of_cachedAction 1970 [5, 2] 7 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1971 : HasPrimeObstruction (representative 1971) := by
  apply obstruction_of_cachedAction 1971 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1972 : HasPrimeObstruction (representative 1972) := by
  apply obstruction_of_cachedAction 1972 [5] 7 1
    (by decide) (by decide) (by decide) 34
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1973 : HasPrimeObstruction (representative 1973) := by
  apply obstruction_of_cachedAction 1973 [5, 1] 5 1
    (by decide) (by decide) (by decide) 198
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1974 : HasPrimeObstruction (representative 1974) := by
  apply obstruction_of_cachedAction 1974 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1975 : HasPrimeObstruction (representative 1975) := by
  apply obstruction_of_cachedAction 1975 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1976 : HasPrimeObstruction (representative 1976) := by
  apply obstruction_of_cachedAction 1976 [5] 7 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1977 : HasPrimeObstruction (representative 1977) := by
  apply obstruction_of_cachedAction 1977 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1978 : HasPrimeObstruction (representative 1978) := by
  apply obstruction_of_cachedAction 1978 [5] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1979 : HasPrimeObstruction (representative 1979) := by
  apply obstruction_of_cachedAction 1979 [5] 5 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1980 : HasPrimeObstruction (representative 1980) := by
  apply obstruction_of_cachedAction 1980 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1981 : HasPrimeObstruction (representative 1981) := by
  apply obstruction_of_cachedAction 1981 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1982 : HasPrimeObstruction (representative 1982) := by
  apply obstruction_of_cachedAction 1982 [5] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1983 : HasPrimeObstruction (representative 1983) := by
  apply obstruction_of_cachedAction 1983 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1984 : HasPrimeObstruction (representative 1984) := by
  apply obstruction_of_cachedAction 1984 [5, 2] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1985 : HasPrimeObstruction (representative 1985) := by
  apply obstruction_of_cachedAction 1985 [5, 1] 7 1
    (by decide) (by decide) (by decide) 38
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1986 : HasPrimeObstruction (representative 1986) := by
  apply obstruction_of_cachedAction 1986 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1987 : HasPrimeObstruction (representative 1987) := by
  apply obstruction_of_cachedAction 1987 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1988 : HasPrimeObstruction (representative 1988) := by
  apply obstruction_of_cachedAction 1988 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1989 : HasPrimeObstruction (representative 1989) := by
  apply obstruction_of_cachedAction 1989 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1990 : HasPrimeObstruction (representative 1990) := by
  apply obstruction_of_cachedAction 1990 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1991 : HasPrimeObstruction (representative 1991) := by
  apply obstruction_of_cachedAction 1991 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1992 : HasPrimeObstruction (representative 1992) := by
  apply obstruction_of_cachedAction 1992 [5, 3] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1993 : HasPrimeObstruction (representative 1993) := by
  apply obstruction_of_cachedAction 1993 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1994 : HasPrimeObstruction (representative 1994) := by
  apply obstruction_of_cachedAction 1994 [5, 4] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1995 : HasPrimeObstruction (representative 1995) := by
  apply obstruction_of_cachedAction 1995 [5, 3] 7 1
    (by decide) (by decide) (by decide) 145
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1996 : HasPrimeObstruction (representative 1996) := by
  apply obstruction_of_cachedAction 1996 [5] 5 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1997 : HasPrimeObstruction (representative 1997) := by
  apply obstruction_of_cachedAction 1997 [5] 7 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1998 : HasPrimeObstruction (representative 1998) := by
  apply obstruction_of_cachedAction 1998 [5] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1999 : HasPrimeObstruction (representative 1999) := by
  apply obstruction_of_cachedAction 1999 [5, 1] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2000 : HasPrimeObstruction (representative 2000) := by
  apply obstruction_of_cachedAction 2000 [5] 7 1
    (by decide) (by decide) (by decide) 37
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2001 : HasPrimeObstruction (representative 2001) := by
  apply obstruction_of_cachedAction 2001 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2002 : HasPrimeObstruction (representative 2002) := by
  apply obstruction_of_cachedAction 2002 [5] 7 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2003 : HasPrimeObstruction (representative 2003) := by
  apply obstruction_of_cachedAction 2003 [5, 2] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2004 : HasPrimeObstruction (representative 2004) := by
  apply obstruction_of_cachedAction 2004 [5, 2] 7 1
    (by decide) (by decide) (by decide) 132
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2005 : HasPrimeObstruction (representative 2005) := by
  apply obstruction_of_cachedAction 2005 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2006 : HasPrimeObstruction (representative 2006) := by
  apply obstruction_of_cachedAction 2006 [5] 5 1
    (by decide) (by decide) (by decide) 24
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2007 : HasPrimeObstruction (representative 2007) := by
  apply obstruction_of_cachedAction 2007 [5] 7 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2008 : HasPrimeObstruction (representative 2008) := by
  apply obstruction_of_cachedAction 2008 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2009 : HasPrimeObstruction (representative 2009) := by
  apply obstruction_of_cachedAction 2009 [5] 7 1
    (by decide) (by decide) (by decide) 21
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2010 : HasPrimeObstruction (representative 2010) := by
  apply obstruction_of_cachedAction 2010 [5] 7 1
    (by decide) (by decide) (by decide) 100
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2011 : HasPrimeObstruction (representative 2011) := by
  apply obstruction_of_cachedAction 2011 [5] 7 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2012 : HasPrimeObstruction (representative 2012) := by
  apply obstruction_of_cachedAction 2012 [5, 1] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2013 : HasPrimeObstruction (representative 2013) := by
  apply obstruction_of_cachedAction 2013 [5] 7 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2014 : HasPrimeObstruction (representative 2014) := by
  apply obstruction_of_cachedAction 2014 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2015 : HasPrimeObstruction (representative 2015) := by
  apply obstruction_of_cachedAction 2015 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2016 : HasPrimeObstruction (representative 2016) := by
  apply obstruction_of_cachedAction 2016 [5, 1] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2017 : HasPrimeObstruction (representative 2017) := by
  apply obstruction_of_cachedAction 2017 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2018 : HasPrimeObstruction (representative 2018) := by
  apply obstruction_of_cachedAction 2018 [5, 3] 7 1
    (by decide) (by decide) (by decide) 451
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2019 : HasPrimeObstruction (representative 2019) := by
  apply obstruction_of_cachedAction 2019 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2020 : HasPrimeObstruction (representative 2020) := by
  apply obstruction_of_cachedAction 2020 [5] 7 1
    (by decide) (by decide) (by decide) 108
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2021 : HasPrimeObstruction (representative 2021) := by
  apply obstruction_of_cachedAction 2021 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2022 : HasPrimeObstruction (representative 2022) := by
  apply obstruction_of_cachedAction 2022 [5] 7 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2023 : HasPrimeObstruction (representative 2023) := by
  apply obstruction_of_cachedAction 2023 [5] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2024 : HasPrimeObstruction (representative 2024) := by
  apply obstruction_of_cachedAction 2024 [5, 2] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2025 : HasPrimeObstruction (representative 2025) := by
  apply obstruction_of_cachedAction 2025 [5, 2] 7 1
    (by decide) (by decide) (by decide) 72
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2026 : HasPrimeObstruction (representative 2026) := by
  apply obstruction_of_cachedAction 2026 [5] 7 1
    (by decide) (by decide) (by decide) 28
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2027 : HasPrimeObstruction (representative 2027) := by
  apply obstruction_of_cachedAction 2027 [5] 7 1
    (by decide) (by decide) (by decide) 45
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2028 : HasPrimeObstruction (representative 2028) := by
  apply obstruction_of_cachedAction 2028 [5] 7 1
    (by decide) (by decide) (by decide) 557
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2029 : HasPrimeObstruction (representative 2029) := by
  apply obstruction_of_cachedAction 2029 [5, 1] 7 1
    (by decide) (by decide) (by decide) 334
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2030 : HasPrimeObstruction (representative 2030) := by
  apply obstruction_of_cachedAction 2030 [5] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2031 : HasPrimeObstruction (representative 2031) := by
  apply obstruction_of_cachedAction 2031 [5] 5 1
    (by decide) (by decide) (by decide) 180
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2032 : HasPrimeObstruction (representative 2032) := by
  apply obstruction_of_cachedAction 2032 [5] 7 1
    (by decide) (by decide) (by decide) 77
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2033 : HasPrimeObstruction (representative 2033) := by
  apply obstruction_of_cachedAction 2033 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2034 : HasPrimeObstruction (representative 2034) := by
  apply obstruction_of_cachedAction 2034 [5] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2035 : HasPrimeObstruction (representative 2035) := by
  apply obstruction_of_cachedAction 2035 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2036 : HasPrimeObstruction (representative 2036) := by
  apply obstruction_of_cachedAction 2036 [5] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2037 : HasPrimeObstruction (representative 2037) := by
  apply obstruction_of_cachedAction 2037 [5] 7 1
    (by decide) (by decide) (by decide) 108
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2038 : HasPrimeObstruction (representative 2038) := by
  apply obstruction_of_cachedAction 2038 [5] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2039 : HasPrimeObstruction (representative 2039) := by
  apply obstruction_of_cachedAction 2039 [5] 7 1
    (by decide) (by decide) (by decide) 301
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2040 : HasPrimeObstruction (representative 2040) := by
  apply obstruction_of_cachedAction 2040 [5, 4] 7 1
    (by decide) (by decide) (by decide) 36
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2041 : HasPrimeObstruction (representative 2041) := by
  apply obstruction_of_cachedAction 2041 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2042 : HasPrimeObstruction (representative 2042) := by
  apply obstruction_of_cachedAction 2042 [5, 3] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2043 : HasPrimeObstruction (representative 2043) := by
  apply obstruction_of_cachedAction 2043 [5] 7 1
    (by decide) (by decide) (by decide) 51
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2044 : HasPrimeObstruction (representative 2044) := by
  apply obstruction_of_cachedAction 2044 [5] 7 1
    (by decide) (by decide) (by decide) 62
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2045 : HasPrimeObstruction (representative 2045) := by
  apply obstruction_of_cachedAction 2045 [5, 2] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2046 : HasPrimeObstruction (representative 2046) := by
  apply obstruction_of_cachedAction 2046 [5] 7 1
    (by decide) (by decide) (by decide) 266
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_2047 : HasPrimeObstruction (representative 2047) := by
  apply obstruction_of_cachedAction 2047 [5] 7 1
    (by decide) (by decide) (by decide) 149
  · decide +kernel
  · decide +kernel

/-- Every nonlocal representative in this interval has a forbidden prime order. -/
public theorem obstruction_block07 (j : Fin 256)
    (h : localBranch ⟨1792 + j.val, by omega⟩ = none) :
    HasPrimeObstruction (representative ⟨1792 + j.val, by omega⟩) := by
  fin_cases j
  · exact obstruction_1792
  · exact obstruction_1793
  · exact obstruction_1794
  · exact obstruction_1795
  · exact obstruction_1796
  · exact obstruction_1797
  · exact obstruction_1798
  · exact obstruction_1799
  · exact obstruction_1800
  · exact obstruction_1801
  · exact obstruction_1802
  · exact obstruction_1803
  · exact obstruction_1804
  · exact obstruction_1805
  · exact obstruction_1806
  · exact obstruction_1807
  · exact obstruction_1808
  · exact obstruction_1809
  · exact obstruction_1810
  · exact obstruction_1811
  · exact obstruction_1812
  · exact obstruction_1813
  · exact obstruction_1814
  · exact obstruction_1815
  · exact obstruction_1816
  · exact obstruction_1817
  · exact obstruction_1818
  · exact obstruction_1819
  · exact obstruction_1820
  · exact obstruction_1821
  · exact obstruction_1822
  · exact obstruction_1823
  · exact obstruction_1824
  · exact obstruction_1825
  · exact obstruction_1826
  · exact obstruction_1827
  · exact obstruction_1828
  · exact obstruction_1829
  · exact obstruction_1830
  · exact obstruction_1831
  · exact obstruction_1832
  · exact obstruction_1833
  · exact obstruction_1834
  · exact obstruction_1835
  · exact obstruction_1836
  · exact obstruction_1837
  · exact obstruction_1838
  · exact obstruction_1839
  · exact obstruction_1840
  · exact obstruction_1841
  · exact obstruction_1842
  · exact obstruction_1843
  · exact obstruction_1844
  · exact obstruction_1845
  · exact obstruction_1846
  · exact obstruction_1847
  · exact obstruction_1848
  · exact obstruction_1849
  · exact obstruction_1850
  · exact obstruction_1851
  · exact obstruction_1852
  · exact obstruction_1853
  · exact obstruction_1854
  · exact obstruction_1855
  · exact obstruction_1856
  · exact obstruction_1857
  · exact obstruction_1858
  · exact obstruction_1859
  · exact obstruction_1860
  · exact obstruction_1861
  · exact obstruction_1862
  · exact obstruction_1863
  · exact obstruction_1864
  · exact obstruction_1865
  · exact obstruction_1866
  · exact obstruction_1867
  · exact obstruction_1868
  · exact obstruction_1869
  · exact obstruction_1870
  · exact obstruction_1871
  · exact obstruction_1872
  · exact obstruction_1873
  · exact obstruction_1874
  · exact obstruction_1875
  · exact obstruction_1876
  · exact obstruction_1877
  · exact obstruction_1878
  · exact obstruction_1879
  · exact obstruction_1880
  · exact obstruction_1881
  · exact obstruction_1882
  · exact obstruction_1883
  · exact obstruction_1884
  · exact obstruction_1885
  · exact obstruction_1886
  · exact obstruction_1887
  · exact obstruction_1888
  · exact obstruction_1889
  · exact obstruction_1890
  · exact obstruction_1891
  · exact obstruction_1892
  · exact obstruction_1893
  · exact obstruction_1894
  · exact obstruction_1895
  · exact obstruction_1896
  · exact obstruction_1897
  · exact obstruction_1898
  · exact obstruction_1899
  · exact obstruction_1900
  · exact obstruction_1901
  · exact obstruction_1902
  · exact obstruction_1903
  · exact obstruction_1904
  · exact obstruction_1905
  · exact obstruction_1906
  · exact obstruction_1907
  · exact obstruction_1908
  · exact obstruction_1909
  · exact obstruction_1910
  · exact obstruction_1911
  · exact obstruction_1912
  · exact obstruction_1913
  · exact obstruction_1914
  · exact obstruction_1915
  · exact obstruction_1916
  · exact obstruction_1917
  · exact obstruction_1918
  · exact obstruction_1919
  · exact obstruction_1920
  · exact obstruction_1921
  · exact obstruction_1922
  · exact obstruction_1923
  · exact obstruction_1924
  · exact obstruction_1925
  · exact obstruction_1926
  · exact obstruction_1927
  · exact obstruction_1928
  · exact obstruction_1929
  · exact obstruction_1930
  · exact obstruction_1931
  · exact obstruction_1932
  · exact obstruction_1933
  · exact obstruction_1934
  · exact obstruction_1935
  · exact obstruction_1936
  · exact obstruction_1937
  · exact obstruction_1938
  · exact obstruction_1939
  · exact obstruction_1940
  · exact obstruction_1941
  · exact obstruction_1942
  · exact obstruction_1943
  · exact obstruction_1944
  · exact obstruction_1945
  · exact obstruction_1946
  · exact obstruction_1947
  · exact obstruction_1948
  · exact obstruction_1949
  · exact obstruction_1950
  · exact obstruction_1951
  · exact obstruction_1952
  · exact obstruction_1953
  · exact obstruction_1954
  · exact obstruction_1955
  · exact obstruction_1956
  · exact obstruction_1957
  · exact obstruction_1958
  · exact obstruction_1959
  · exact obstruction_1960
  · exact obstruction_1961
  · exact obstruction_1962
  · exact obstruction_1963
  · exact obstruction_1964
  · exact obstruction_1965
  · exact obstruction_1966
  · exact obstruction_1967
  · exact obstruction_1968
  · exact obstruction_1969
  · exact obstruction_1970
  · exact obstruction_1971
  · exact obstruction_1972
  · exact obstruction_1973
  · exact obstruction_1974
  · exact obstruction_1975
  · exact obstruction_1976
  · exact obstruction_1977
  · exact obstruction_1978
  · exact obstruction_1979
  · exact obstruction_1980
  · exact obstruction_1981
  · exact obstruction_1982
  · exact obstruction_1983
  · exact obstruction_1984
  · exact obstruction_1985
  · exact obstruction_1986
  · exact obstruction_1987
  · exact obstruction_1988
  · exact obstruction_1989
  · exact obstruction_1990
  · exact obstruction_1991
  · exact obstruction_1992
  · exact obstruction_1993
  · exact obstruction_1994
  · exact obstruction_1995
  · exact obstruction_1996
  · exact obstruction_1997
  · exact obstruction_1998
  · exact obstruction_1999
  · exact obstruction_2000
  · exact obstruction_2001
  · exact obstruction_2002
  · exact obstruction_2003
  · exact obstruction_2004
  · exact obstruction_2005
  · exact obstruction_2006
  · exact obstruction_2007
  · exact obstruction_2008
  · exact obstruction_2009
  · exact obstruction_2010
  · exact obstruction_2011
  · exact obstruction_2012
  · exact obstruction_2013
  · exact obstruction_2014
  · exact obstruction_2015
  · exact obstruction_2016
  · exact obstruction_2017
  · exact obstruction_2018
  · exact obstruction_2019
  · exact obstruction_2020
  · exact obstruction_2021
  · exact obstruction_2022
  · exact obstruction_2023
  · exact obstruction_2024
  · exact obstruction_2025
  · exact obstruction_2026
  · exact obstruction_2027
  · exact obstruction_2028
  · exact obstruction_2029
  · exact obstruction_2030
  · exact obstruction_2031
  · exact obstruction_2032
  · exact obstruction_2033
  · exact obstruction_2034
  · exact obstruction_2035
  · exact obstruction_2036
  · exact obstruction_2037
  · exact obstruction_2038
  · exact obstruction_2039
  · exact obstruction_2040
  · exact obstruction_2041
  · exact obstruction_2042
  · exact obstruction_2043
  · exact obstruction_2044
  · exact obstruction_2045
  · exact obstruction_2046
  · exact obstruction_2047

end Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification
