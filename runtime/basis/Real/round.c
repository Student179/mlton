#include <math.h>
#include "mlton-basis.h"

#if (defined (__i386__))

Double Real_round (Double d) {
	register double f0;

	f0 = d;
	__asm__ __volatile__ ("frndint"
			: "=t" (f0)
			: "0" (f0));
	return f0;

}

#elif (defined __sparc__)

Double Real_round (Double d) {
	return rint (d);
}

#else

#error Real_round not defined

#endif
